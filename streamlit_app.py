#!/usr/bin/env python3
"""
Universal PDF Extractor - Streamlit Web App (PDF-Only Architecture)
-------------------------------------------------------------------
Rock-solid, dedicated PDF harvesting engine for DSpace repositories,
academic portals, and educational resource websites.
"""

from __future__ import annotations

import csv
import io
import re
import time
import zipfile
import tempfile
import shutil
import gc
from collections import deque
from dataclasses import dataclass
from html import unescape
from pathlib import Path, PurePosixPath
from urllib.parse import urljoin, urlparse, urldefrag, unquote, urlsplit, urlunsplit

import urllib3
import requests
from bs4 import BeautifulSoup
import streamlit as st
try:
    import pandas as pd
    HAS_PANDAS = True
except Exception:
    HAS_PANDAS = False

# Optional pypdf for reading internal PDF metadata
try:
    import pypdf
    HAS_PYPDF = True
except Exception:
    HAS_PYPDF = False

# Suppress insecure SSL warnings for educational/institutional portals
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/128.0.0.0 Safari/537.36"
)
HANDLE_RE = re.compile(r"/handle/(\d+)/([^/?#]+)", re.I)
DSPACE_HANDLE_STRICT = re.compile(r"^/handle/(\d+)/([a-zA-Z0-9_.\-]+)$", re.I)
BAD_CHARS = re.compile(r'[<>:"/\\|?*\x00-\x1f]')
WINDOWS_RESERVED = {
    "CON", "PRN", "AUX", "NUL",
    *(f"COM{i}" for i in range(1, 10)),
    *(f"LPT{i}" for i in range(1, 10)),
}
SKIPPABLE_EXTENSIONS = {
    ".pdf", ".png", ".jpg", ".jpeg", ".gif", ".webp", ".svg", ".ico",
    ".css", ".js", ".mp4", ".mp3", ".zip", ".tar", ".gz", ".7z",
    ".exe", ".dmg", ".apk"
}


def clean_text(value: str) -> str:
    return re.sub(r"\s+", " ", unescape(value or "")).strip()


def safe_filename(name: str, fallback: str = "document.pdf") -> str:
    name = unquote(name or "").strip()
    name = BAD_CHARS.sub("_", name)
    name = name.strip(" .")
    if not name:
        name = fallback
    stem = name[:-4] if name.lower().endswith(".pdf") else name
    if stem.upper() in WINDOWS_RESERVED:
        name = f"doc_{name}"
    if not name.lower().endswith(".pdf"):
        name += ".pdf"
    return name[:180]


def safe_folder_name(name: str, fallback: str = "harvested_pdfs") -> str:
    name = unquote(name or "").strip()
    name = BAD_CHARS.sub("_", name)
    name = name.strip(" .")
    if not name:
        name = fallback
    if name.upper() in WINDOWS_RESERVED:
        name = f"folder_{name}"
    return name[:120]


def clean_url(url: str) -> str:
    parsed = urlsplit(url)
    path = parsed.path
    while "//" in path:
        path = path.replace("//", "/")
    return urlunsplit((parsed.scheme, parsed.netloc, path, parsed.query, parsed.fragment))


def canonical(url: str) -> str:
    url, _ = urldefrag(clean_url(url))
    return url.rstrip("/")


def normalize_host(netloc: str) -> str:
    h = netloc.lower().split(":")[0]
    return h[4:] if h.startswith("www.") else h


def same_site(url: str, host: str) -> bool:
    return normalize_host(urlparse(url).netloc) == normalize_host(host)


def is_valid_pdf_bitstream(href: str) -> bool:
    """Rejects DSpace thumbnail image bundles (.jpg, .png) and non-PDF bitstreams."""
    u = urlparse(href)
    p = u.path.lower()
    if any(p.endswith(ext) for ext in (".jpg", ".jpeg", ".png", ".gif", ".webp", ".txt", ".mp4", ".mp3")):
        return False
    if any(ext in href.lower() for ext in (".jpg?", ".jpeg?", ".png?", ".gif?", ".webp?", "thumbnail")):
        return False
    return True


POSTBACK_RE = re.compile(r"""__doPostBack\(\s*['"]([^'"]+)['"]\s*,\s*['"]([^'"]*)['"]\s*\)""", re.I)


def extract_aspnet_form_data(soup: BeautifulSoup) -> dict:
    """Extracts hidden fields (__VIEWSTATE, __EVENTVALIDATION) and control states for ASP.NET postbacks."""
    data = {}
    form = soup.find("form") or soup
    for inp in form.find_all("input"):
        n = inp.get("name")
        v = inp.get("value", "")
        if n:
            data[n] = v
    for sel in form.find_all("select"):
        n = sel.get("name")
        if n:
            opt = sel.find("option", selected=True) or sel.find("option")
            if opt and opt.get("value") is not None:
                data[n] = opt.get("value")
    return data


def is_pdf_url(url: str) -> bool:
    path = urlparse(url).path.lower()
    return path.endswith(".pdf") or ".pdf?" in url.lower() or "/bitstream/" in path


def extract_pdf_file_metadata(pdf_path: Path) -> dict:
    """Reads embedded author, title, creation date, and subject directly from PDF."""
    info = {}
    if HAS_PYPDF and pdf_path.exists():
        try:
            reader = pypdf.PdfReader(pdf_path)
            raw = reader.metadata or {}
            if raw.get("/Title"):
                info["title"] = clean_text(str(raw.get("/Title")))
            if raw.get("/Author"):
                info["authors"] = clean_text(str(raw.get("/Author")))
            if raw.get("/Subject"):
                info["subject"] = clean_text(str(raw.get("/Subject")))
            if raw.get("/CreationDate"):
                d = str(raw.get("/CreationDate"))
                m = re.search(r"(\d{4})(\d{2})(\d{2})", d)
                if m:
                    info["date"] = f"{m.group(1)}-{m.group(2)}-{m.group(3)}"
                else:
                    info["date"] = d
            if raw.get("/Creator") or raw.get("/Producer"):
                info["publisher"] = clean_text(str(raw.get("/Creator") or raw.get("/Producer")))
        except Exception:
            pass
    return info


@dataclass
class DownloadRecord:
    title: str
    authors: str
    date: str
    publisher: str
    subject: str
    description: str
    language: str
    item_type: str
    page_url: str
    pdf_url: str
    filename: str
    size_bytes: int
    status: str
    error: str


class WebDownloader:
    def __init__(self, start_url: str, delay: float = 0.5,
                 timeout: int = 40, max_pages: int = 150,
                 max_depth: int = 2, status_container=None):
        self.start_url = canonical(start_url)
        self.host = urlparse(start_url).netloc
        self.delay = delay
        self.timeout = timeout
        self.max_pages = max_pages
        self.max_depth = max_depth
        self.status_container = status_container

        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": USER_AGENT,
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,application/pdf,*/*;q=0.8",
            "Accept-Language": "en-US,en;q=0.9",
            "Connection": "keep-alive",
        })

        self.visited = set()
        self.records: list[DownloadRecord] = []
        self.pdf_url_seen = set()
        self.downloaded_files: list[tuple[str, Path, str]] = []
        self.temp_dir: Path | None = None
        self.is_dspace_repo = False

    def log(self, message: str):
        if self.status_container:
            self.status_container.write(message)

    def get(self, url: str, stream: bool = False, headers: dict | None = None):
        last_error = None
        req_headers = dict(self.session.headers)
        if headers:
            req_headers.update(headers)

        for attempt in range(3):
            try:
                response = self.session.get(
                    url,
                    headers=req_headers,
                    timeout=self.timeout,
                    stream=stream,
                    allow_redirects=True,
                    verify=False,
                )
                response.raise_for_status()
                return response
            except Exception as exc:
                last_error = exc
                time.sleep(1.0 * (attempt + 1))
        raise last_error

    def detect_mode(self, first_soup: BeautifulSoup, first_url: str):
        if HANDLE_RE.search(urlparse(first_url).path):
            self.is_dspace_repo = True
        elif first_soup.select_one("table.itemDisplayTable") or first_soup.find("meta", attrs={"name": re.compile(r"citation_pdf_url", re.I)}):
            self.is_dspace_repo = True
        elif "dspace" in first_soup.get_text(" ", strip=True).lower() or "/bitstream/" in str(first_soup):
            self.is_dspace_repo = True
        else:
            self.is_dspace_repo = False

        engine_name = "DSpace Academic Engine" if self.is_dspace_repo else "Document Portal Engine"
        self.log(f"🔎 **Active Engine:** {engine_name}")

    def crawl(self, progress_bar=None):
        queue = deque([(self.start_url, 0)])
        first_page = True

        while queue and len(self.visited) < self.max_pages:
            url, depth = queue.popleft()
            url = canonical(url)
            if url in self.visited:
                continue
            self.visited.add(url)

            if progress_bar:
                progress_bar.progress(min(1.0, len(self.visited) / max(1, self.max_pages)))

            try:
                if self.delay:
                    time.sleep(self.delay)

                response = self.get(url)
                content_type = response.headers.get("content-type", "").lower()

                # Direct PDF URL
                if "application/pdf" in content_type or url.lower().endswith(".pdf"):
                    filename = safe_filename(PurePosixPath(urlparse(url).path).name)
                    self.download_pdf(url, filename, url, page_title=filename[:-4], meta={})
                    continue

                if "text/html" not in content_type and "application/xhtml" not in content_type:
                    continue

                soup = BeautifulSoup(response.text, "html.parser")
                if first_page:
                    self.detect_mode(soup, response.url)
                    first_page = False

                self.log(f"📄 Explored: `{url}`")

                if self.is_dspace_repo:
                    self.process_dspace(soup, response.url, queue, depth)
                else:
                    self.process_generic(soup, response.url, queue, depth)

                response.close()
                del response
                del soup
                if len(self.visited) % 10 == 0:
                    gc.collect()

            except Exception as exc:
                self.log(f"⚠️ Could not load `{url}`: {exc}")

    def process_dspace(self, soup: BeautifulSoup, page_url: str, queue: deque, depth: int):
        # 1. On starting page, blacklist parent breadcrumbs to prevent crawling upwards into parent university faculties
        if depth == 0:
            for b in soup.find_all(["ol", "ul", "div", "nav"], class_=lambda c: c and any(w in str(c).lower() for w in ("breadcrumb", "trail", "breadcrumbs"))):
                for a in b.find_all("a", href=True):
                    self.visited.add(canonical(urljoin(page_url, a["href"])))

        # 2. Extract direct bitstream PDF links if present on this page (works across both DSpace JSPUI & XMLUI)
        pdf_links = self.extract_dspace_pdf_links(soup, page_url)
        if pdf_links:
            meta = self.extract_dspace_metadata(soup)
            for pdf_url, label in pdf_links:
                raw_name = label or PurePosixPath(urlparse(pdf_url).path).name
                filename = safe_filename(raw_name)
                self.download_pdf(pdf_url, filename, page_url, meta=meta)
            return

        # 3. Community / Collection index: queue child sub-communities, collections, and items
        if depth < self.max_depth:
            main = soup.find("main") or soup.find(id="content") or soup.find("div", class_="container") or soup.body or soup
            for a in main.find_all("a", href=True):
                # Skip breadcrumbs, headers, footers, search facets, and sidebars
                if a.find_parent(class_=lambda c: c and any(w in str(c).lower() for w in ("breadcrumb", "trail", "header", "footer", "sidebar", "facet", "browse"))):
                    continue
                raw_href = a["href"].strip()
                if any(w in raw_href.lower() for w in ("simple-search", "browse?", "login", "register", "password", "signon", "?mode=full")):
                    continue

                child_url = canonical(urljoin(page_url, raw_href))
                u = urlparse(child_url)
                if same_site(child_url, self.host) and DSPACE_HANDLE_STRICT.match(u.path.rstrip("/")):
                    if child_url not in self.visited and not any(child_url == q_url for q_url, _ in queue):
                        queue.append((child_url, depth + 1))

    def extract_generic_page_metadata(self, soup: BeautifulSoup, page_url: str) -> dict:
        meta = {}
        meta["title"] = clean_text(soup.title.get_text(" ", strip=True)) if soup.title else ""
        meta["publisher"] = urlparse(page_url).netloc

        for tag in soup.find_all("meta"):
            name = (tag.get("name") or tag.get("property") or "").lower()
            content = clean_text(tag.get("content", ""))
            if not content:
                continue

            if name in ("description", "og:description", "twitter:description", "dc.description"):
                meta.setdefault("description", content)
            elif name in ("author", "article:author", "dc.creator", "dc.contributor"):
                meta.setdefault("authors", content)
            elif name in ("date", "pubdate", "article:published_time", "dc.date", "dc.date.issued"):
                meta.setdefault("date", content)
            elif name in ("publisher", "og:site_name", "dc.publisher"):
                meta["publisher"] = content
            elif name in ("keywords", "subject", "dc.subject"):
                meta.setdefault("subject", content)
            elif name in ("language", "dc.language", "og:locale"):
                meta.setdefault("language", content)

        return meta

    def process_generic(self, soup: BeautifulSoup, page_url: str, queue: deque, depth: int):
        page_meta = self.extract_generic_page_metadata(soup, page_url)

        # 1. Parse tables: extract title, date, and PDF link
        for table in soup.find_all("table"):
            headers = [clean_text(th.get_text(" ", strip=True)).lower() for th in table.find_all("th")]
            date_col_idx = -1
            for idx, h in enumerate(headers):
                if any(w in h for w in ("date", "year", "session", "published", "issue")):
                    date_col_idx = idx
                    break

            for row in table.find_all("tr"):
                cells = row.find_all(["td", "th"])
                if len(cells) >= 2:
                    first_cell_text = clean_text(cells[0].get_text(" ", strip=True))
                    row_meta = dict(page_meta)
                    if date_col_idx != -1 and date_col_idx < len(cells):
                        d_text = clean_text(cells[date_col_idx].get_text(" ", strip=True))
                        if d_text:
                            row_meta["date"] = d_text

                    for a in row.find_all("a", href=True):
                        raw_href = a["href"].strip()
                        link_text = clean_text(a.get_text(" ", strip=True))
                        title = first_cell_text if len(first_cell_text) > 3 else (link_text or PurePosixPath(urlparse(page_url).path).name)
                        filename = safe_filename(title)
                        row_meta["title"] = title

                        # 1. Support ASP.NET __doPostBack LinkButtons (e.g., WBCSC SET Question Papers)
                        m_post = POSTBACK_RE.search(unescape(raw_href))
                        if m_post:
                            target, arg = m_post.group(1), m_post.group(2)
                            if any(w in link_text.lower() for w in ("download", "view", "pdf", "lnkdelete", "lnkdownload", "click")) or any(w in first_cell_text.lower() for w in ("paper", "general", "set", "syllabus", "subject")):
                                self.download_aspnet_postback(page_url, soup, target, arg, filename, meta=row_meta, page_title=title)
                                continue

                        if not raw_href or raw_href.lower().startswith(("javascript:", "mailto:", "tel:", "#")):
                            continue
                        href = urljoin(page_url, raw_href)
                        if urlparse(href).scheme not in ("http", "https"):
                            continue
                        if is_pdf_url(href) or any(w in link_text.lower() for w in ("view(", "accessible version", "download", "pdf")):
                            self.download_pdf(href, filename, page_url, meta=row_meta, page_title=title)

        # 2. Parse any direct PDF links outside tables
        for a in soup.find_all("a", href=True):
            raw_href = a["href"].strip()
            if not raw_href or raw_href.lower().startswith(("javascript:", "mailto:", "tel:", "#")):
                continue
            href = urljoin(page_url, raw_href)
            if urlparse(href).scheme not in ("http", "https"):
                continue
            link_text = clean_text(a.get_text(" ", strip=True))
            if is_pdf_url(href):
                raw_name = link_text if link_text and not any(w in link_text.lower() for w in ["pdf", "download", "view", "link"]) else PurePosixPath(urlparse(href).path).name
                filename = safe_filename(raw_name or PurePosixPath(urlparse(href).path).name)

                link_meta = dict(page_meta)
                link_meta["title"] = raw_name or link_meta.get("title", filename)
                self.download_pdf(href, filename, page_url, meta=link_meta, page_title=link_meta["title"])

        # 3. Follow subpages within depth limit
        if depth < self.max_depth:
            for a in soup.find_all("a", href=True):
                raw_href = a["href"].strip()
                if not raw_href or raw_href.lower().startswith(("javascript:", "mailto:", "tel:", "#")):
                    continue
                href = canonical(urljoin(page_url, raw_href))
                u = urlparse(href)
                if u.scheme not in ("http", "https") or not same_site(href, self.host):
                    continue
                if u.path.lower().endswith(".pdf") or ".pdf?" in href.lower():
                    continue
                if any(u.path.lower().endswith(ext) for ext in SKIPPABLE_EXTENSIONS):
                    continue
                if href not in self.visited and not any(href == q_url for q_url, _ in queue):
                    queue.append((href, depth + 1))

        # 4. Automatic ASP.NET Dropdown Session Exploration (e.g. WBCSC SETQuestionPaper.aspx)
        if (page_url.lower().endswith(".aspx") or soup.find("input", attrs={"name": "__VIEWSTATE"})):
            self.process_aspnet_dropdowns(soup, page_url, queue, depth)

    def extract_dspace_pdf_links(self, soup: BeautifulSoup, page_url: str):
        found = []
        seen_paths = set()
        generic_labels = {"view", "open", "view/open", "download", "show", "thumbnail", ""}

        for table in soup.find_all("table"):
            for row in table.find_all("tr"):
                cells = row.find_all(["td", "th"])
                # Exclude image thumbnails and non-PDF bitstreams
                row_links = [
                    urljoin(page_url, a["href"]) 
                    for a in row.find_all("a", href=True) 
                    if "/bitstream/" in a["href"].lower() and is_valid_pdf_bitstream(a["href"])
                ]
                if not row_links:
                    continue

                filename = ""
                for a in row.find_all("a", href=True):
                    txt = clean_text(a.get_text(" ", strip=True))
                    if txt and txt.lower() not in generic_labels and is_valid_pdf_bitstream(a["href"]):
                        filename = txt
                        break
                if not filename and cells:
                    for c in cells:
                        c_text = clean_text(c.get_text(" ", strip=True))
                        if c_text and c_text.lower() not in generic_labels and not any(w in c_text.lower() for w in ("adobe", "mb", "kb", "format", "size", "thumbnail")):
                            filename = c_text
                            break

                # Prioritize direct .pdf links over non-extension URLs
                best_link = row_links[0]
                for l in row_links:
                    if l.lower().endswith(".pdf") or ".pdf?" in l.lower():
                        best_link = l
                        break

                u = urlparse(best_link)
                if u.path.lower() in seen_paths:
                    continue
                seen_paths.add(u.path.lower())

                if not filename:
                    filename = PurePosixPath(u.path).name

                found.append((best_link, filename))

        for a in soup.find_all("a", href=True):
            raw_href = a["href"].strip()
            if not is_valid_pdf_bitstream(raw_href):
                continue
            href = urljoin(page_url, raw_href)
            u = urlparse(href)
            if "/bitstream/" in u.path.lower() and u.path.lower() not in seen_paths:
                label = clean_text(a.get_text(" ", strip=True))
                name = PurePosixPath(u.path).name
                final_name = name if label.lower() in generic_labels else (label or name)
                seen_paths.add(u.path.lower())
                found.append((href, final_name))

        return found

    def extract_dspace_metadata(self, soup: BeautifulSoup):
        data = {}
        for tag in soup.find_all("meta"):
            key = (tag.get("name") or "").strip()
            value = clean_text(tag.get("content", ""))
            if key and value and (key.lower().startswith("dc.") or key.lower().startswith("dcterms.") or key.lower().startswith("citation_")):
                data.setdefault(key, []).append(value)

        table = soup.select_one("table.itemDisplayTable")
        if table:
            for row in table.select("tr"):
                cells = row.find_all(["td", "th"], recursive=False)
                if len(cells) >= 2:
                    k = clean_text(cells[0].get_text(" ", strip=True)).rstrip(":")
                    v = clean_text(cells[1].get_text(" ", strip=True))
                    if k and v:
                        data.setdefault(k, []).append(v)

        def first(*keys):
            for k in keys:
                vals = data.get(k)
                if vals:
                    return "; ".join(vals)
            return ""

        title = first("DC.title", "dc.title", "citation_title", "Title") or (clean_text(soup.title.get_text(" ", strip=True)) if soup.title else "")
        return {
            "title": title,
            "authors": first("DC.contributor.author", "dc.contributor.author", "citation_author", "Authors", "Author"),
            "date": first("DCTERMS.issued", "dc.date.issued", "citation_date", "Issue Date"),
            "publisher": first("DC.publisher", "dc.publisher", "Publisher"),
            "subject": first("DC.subject", "dc.subject", "Subject"),
            "description": first("DC.description", "dc.description", "Description"),
            "language": first("DC.language", "dc.language", "citation_language"),
            "type": first("DC.type", "dc.type", "Type"),
        }

    def download_aspnet_postback(self, page_url: str, soup: BeautifulSoup, target: str, argument: str,
                                 base_filename: str, meta: dict | None = None, page_title: str = ""):
        """Executes an ASP.NET __doPostBack to stream server-generated PDFs (e.g. WBCSC question papers)."""
        post_key = f"{page_url}#{target}#{argument}"
        if post_key in self.pdf_url_seen:
            return
        self.pdf_url_seen.add(post_key)

        meta = dict(meta or {})
        item_title = meta.get("title") or page_title or base_filename

        stem = base_filename[:-4] if base_filename.lower().endswith(".pdf") else base_filename
        target_path = self.temp_dir / base_filename
        counter = 2
        existing_names = {f for f, _, _ in self.downloaded_files}
        while target_path.exists() or target_path.name in existing_names:
            target_path = self.temp_dir / f"{stem}_{counter}.pdf"
            counter += 1

        filename = target_path.name
        self.log(f"⬇️ Downloading (ASP.NET): **{filename}**")

        try:
            if self.delay:
                time.sleep(self.delay)

            data = extract_aspnet_form_data(soup)
            data["__EVENTTARGET"] = target
            data["__EVENTARGUMENT"] = argument

            response = self.session.post(
                page_url,
                data=data,
                headers={"Referer": page_url},
                timeout=self.timeout,
                stream=True,
                verify=False,
            )
            response.raise_for_status()

            content_type = response.headers.get("content-type", "").lower()
            content_disp = response.headers.get("content-disposition", "")
            if "filename=" in content_disp:
                m_fn = re.search(r"""filename=["']?([^"';]+)""", content_disp)
                if m_fn:
                    parsed_fn = safe_filename(m_fn.group(1))
                    if parsed_fn:
                        filename = parsed_fn
                        target_path = self.temp_dir / filename

            total = 0
            signature = b""
            with target_path.open("wb") as output:
                for chunk in response.iter_content(chunk_size=1024 * 128):
                    if not chunk:
                        continue
                    if len(signature) < 1024:
                        signature += chunk[:1024 - len(signature)]
                    output.write(chunk)
                    total += len(chunk)
            response.close()

            # Clean and robust PDF signature verification
            if b"%PDF-" not in signature:
                target_path.unlink(missing_ok=True)
                raise ValueError(f"Content is not a PDF (content-type: '{content_type or 'unknown'}')")

            pdf_internal_meta = extract_pdf_file_metadata(target_path)
            for k, v in pdf_internal_meta.items():
                if not meta.get(k) and v:
                    meta[k] = v

            self.downloaded_files.append((filename, target_path, page_url))
            self.records.append(DownloadRecord(
                title=meta.get("title") or item_title,
                authors=meta.get("authors", ""),
                date=meta.get("date", ""),
                publisher=meta.get("publisher", ""),
                subject=meta.get("subject", ""),
                description=meta.get("description", ""),
                language=meta.get("language", ""),
                item_type="PDF Document",
                page_url=page_url,
                pdf_url=page_url,
                filename=filename,
                size_bytes=total,
                status="Downloaded",
                error="",
            ))
        except Exception as exc:
            target_path.unlink(missing_ok=True)
            self.records.append(DownloadRecord(
                title=item_title,
                authors=meta.get("authors", ""),
                date=meta.get("date", ""),
                publisher=meta.get("publisher", ""),
                subject=meta.get("subject", ""),
                description=meta.get("description", ""),
                language=meta.get("language", ""),
                item_type="PDF Document",
                page_url=page_url,
                pdf_url=page_url,
                filename=filename,
                size_bytes=0,
                status="Failed",
                error=str(exc),
            ))
            self.log(f"❌ Failed `{filename}`: {exc}")

    def process_aspnet_dropdowns(self, soup: BeautifulSoup, page_url: str, queue: deque, depth: int):
        """Automatically loops through ASP.NET examination session dropdowns (e.g. SET 27th, 26th, etc.)."""
        form_data = extract_aspnet_form_data(soup)
        if "__VIEWSTATE" not in form_data:
            return

        for sel in soup.find_all("select"):
            sel_name = sel.get("name")
            if not sel_name:
                continue

            for opt in sel.find_all("option"):
                opt_val = opt.get("value", "").strip()
                opt_text = clean_text(opt.get_text(" ", strip=True))
                if not opt_val or opt_val in ("0", "-1", "") or opt_text.startswith("--") or "select" in opt_text.lower():
                    continue

                session_key = f"{page_url}?{sel_name}={opt_val}"
                if session_key in self.visited:
                    continue
                self.visited.add(session_key)

                try:
                    self.log(f"🔎 Exploring Examination Session: **{opt_text}**")
                    payload = dict(form_data)
                    payload["__EVENTTARGET"] = sel_name
                    payload["__EVENTARGUMENT"] = ""
                    payload[sel_name] = opt_val

                    res = self.session.post(
                        page_url,
                        data=payload,
                        headers={"Referer": page_url},
                        timeout=self.timeout,
                        verify=False
                    )
                    if res.status_code == 200 and "text/html" in res.headers.get("content-type", ""):
                        sub_soup = BeautifulSoup(res.text, "html.parser")
                        self.process_generic(sub_soup, page_url, queue, depth + 1)
                        del sub_soup
                    res.close()
                    del res
                    gc.collect()
                except Exception as exc:
                    self.log(f"⚠️ Could not load session `{opt_text}`: {exc}")

    def download_pdf(self, pdf_url: str, base_filename: str, page_url: str,
                     meta: dict | None = None, page_title: str = ""):
        if not pdf_url or urlparse(pdf_url).scheme not in ("http", "https"):
            return
        if pdf_url in self.pdf_url_seen:
            return
        self.pdf_url_seen.add(pdf_url)

        meta = dict(meta or {})
        item_title = meta.get("title") or page_title or base_filename

        stem = base_filename[:-4] if base_filename.lower().endswith(".pdf") else base_filename
        target_path = self.temp_dir / base_filename
        counter = 2
        existing_names = {f for f, _, _ in self.downloaded_files}
        while target_path.exists() or target_path.name in existing_names:
            target_path = self.temp_dir / f"{stem}_{counter}.pdf"
            counter += 1

        filename = target_path.name
        self.log(f"⬇️ Downloading: **{filename}**")

        try:
            if self.delay:
                time.sleep(self.delay)

            response = self.get(pdf_url, stream=True, headers={"Referer": page_url})
            content_type = response.headers.get("content-type", "").lower()

            total = 0
            signature = b""
            with target_path.open("wb") as output:
                for chunk in response.iter_content(chunk_size=1024 * 128):
                    if not chunk:
                        continue
                    if len(signature) < 1024:
                        signature += chunk[:1024 - len(signature)]
                    output.write(chunk)
                    total += len(chunk)
            response.close()

            # Clean and robust PDF signature verification
            if b"%PDF-" not in signature:
                target_path.unlink(missing_ok=True)
                raise ValueError(f"Content is not a PDF (content-type: '{content_type or 'unknown'}')")

            # Extract internal PDF metadata if available
            pdf_internal_meta = extract_pdf_file_metadata(target_path)
            for k, v in pdf_internal_meta.items():
                if not meta.get(k) and v:
                    meta[k] = v

            self.downloaded_files.append((filename, target_path, pdf_url))
            self.records.append(DownloadRecord(
                title=meta.get("title") or item_title,
                authors=meta.get("authors", ""),
                date=meta.get("date", ""),
                publisher=meta.get("publisher", ""),
                subject=meta.get("subject", ""),
                description=meta.get("description", ""),
                language=meta.get("language", ""),
                item_type="PDF Document",
                page_url=page_url,
                pdf_url=pdf_url,
                filename=filename,
                size_bytes=total,
                status="Downloaded",
                error="",
            ))
        except Exception as exc:
            target_path.unlink(missing_ok=True)
            self.records.append(DownloadRecord(
                title=item_title,
                authors=meta.get("authors", ""),
                date=meta.get("date", ""),
                publisher=meta.get("publisher", ""),
                subject=meta.get("subject", ""),
                description=meta.get("description", ""),
                language=meta.get("language", ""),
                item_type="PDF Document",
                page_url=page_url,
                pdf_url=pdf_url,
                filename=filename,
                size_bytes=0,
                status="Failed",
                error=str(exc),
            ))
            self.log(f"❌ Failed `{filename}`: {exc}")


def build_zip_on_disk(downloaded_files, records, output_zip_path: Path, folder_name: str = "harvested_pdfs") -> None:
    """Builds the ZIP bundle directly on disk to prevent RAM usage on Streamlit Cloud."""
    output_zip_path.parent.mkdir(parents=True, exist_ok=True)
    clean_folder = safe_folder_name(folder_name)
    with zipfile.ZipFile(output_zip_path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for filename, local_path, _ in downloaded_files:
            try:
                if local_path.exists():
                    zf.write(local_path, f"{clean_folder}/PDFs/{filename}")
            except Exception:
                pass

        csv_buf = io.StringIO()
        fieldnames = [
            "title", "authors", "date", "publisher", "subject",
            "description", "language", "item_type", "page_url",
            "pdf_url", "filename", "size_bytes", "status", "error"
        ]
        writer = csv.DictWriter(csv_buf, fieldnames=fieldnames)
        writer.writeheader()
        for rec in records:
            writer.writerow(rec.__dict__)
        zf.writestr(f"{clean_folder}/metadata.csv", ("\ufeff" + csv_buf.getvalue()).encode("utf-8"))


# -------------------------------------------------------------
# Streamlit UI Configuration
# -------------------------------------------------------------
st.set_page_config(
    page_title="PDF Extractor",
    page_icon="🎓",
    layout="wide",
)

st.markdown(
    """
    <head>
        <title>PDF Extractor</title>
        <meta property="og:title" content="PDF Extractor" />
        <meta property="og:description" content="Universal Bulk Document Harvesting & PDF Extractor" />
        <meta property="og:site_name" content="PDF Extractor" />
        <meta property="og:type" content="website" />
        <meta name="twitter:title" content="PDF Extractor" />
        <meta name="twitter:description" content="Universal Bulk Document Harvesting & PDF Extractor" />
    </head>
    """,
    unsafe_allow_html=True,
)

# Custom Styling
st.markdown(
    """
    <style>
    @import url('https://fonts.googleapis.com/css2?family=Plus+Jakarta+Sans:wght@400;500;600;700;800&family=Cinzel:wght@700;800&display=swap');

    .stApp {
        background: #f4f7fb;
        font-family: 'Plus Jakarta Sans', sans-serif;
    }

    /* Main Header Card with Golden & White Typography */
    .system-header-card {
        background: linear-gradient(135deg, #021a44 0%, #082d6c 60%, #031e50 100%);
        border-bottom: 3px solid #d4af37;
        border-radius: 14px;
        padding: 18px 24px;
        display: flex;
        align-items: center;
        justify-content: space-between;
        margin-bottom: 18px;
        box-shadow: 0 6px 20px rgba(2, 26, 68, 0.12);
    }
    .system-header-left {
        display: flex;
        align-items: center;
        gap: 14px;
    }
    .system-header-icon {
        background: #1e40af;
        border: 2px solid #d4af37;
        color: #ffd700;
        width: 46px;
        height: 46px;
        border-radius: 12px;
        display: flex;
        align-items: center;
        justify-content: center;
        font-size: 24px;
        box-shadow: 0 4px 12px rgba(0,0,0,0.15);
    }

    /* Force dark, readable font on ALL widgets on mobile */
    .stRadio label, .stRadio div, .stRadio p, .stRadio span {
        color: #0f172a !important;
        font-weight: 600 !important;
    }
    .stSlider label, .stSlider div, .stSlider p, .stSlider span {
        color: #0f172a !important;
        font-weight: 600 !important;
    }
    .stNumberInput label, .stNumberInput div, .stNumberInput p, .stNumberInput span, .stNumberInput input {
        color: #0f172a !important;
        font-weight: 600 !important;
    }
    .streamlit-expanderHeader, [data-testid="stExpander"] summary, [data-testid="stExpander"] details summary p {
        color: #0f172a !important;
        font-weight: 700 !important;
    }
    [data-testid="stExpander"] {
        background-color: #f8faff !important;
        border: 1px solid #bfdbfe !important;
        border-radius: 10px !important;
    }
    [data-testid="stExpander"] * {
        color: #0f172a !important;
    }

    /* Title: PDF Extractor in Brilliant Golden */
    .system-title,
    h1.system-title,
    div.system-title,
    .stApp .system-title {
        font-family: 'Cinzel', 'Plus Jakarta Sans', serif, sans-serif !important;
        font-size: 30px !important;
        font-weight: 800 !important;
        color: #ffd700 !important;
        -webkit-text-fill-color: #ffd700 !important;
        margin: 0 !important;
        letter-spacing: 1px !important;
        text-shadow: 0 2px 10px rgba(0, 0, 0, 0.5) !important;
    }
    .system-subtitle {
        font-size: 13px;
        font-weight: 500;
        color: #ffffff !important;
        margin: 0;
        letter-spacing: 0.4px;
    }
    .system-badge-right {
        background: rgba(255, 255, 255, 0.12);
        border: 1px solid rgba(212, 175, 55, 0.5);
        color: #ffd700;
        font-weight: 700;
        font-size: 13px;
        padding: 6px 14px;
        border-radius: 20px;
    }

    /* PROMINENTLY HIGHLIGHTED URL INPUT CONTAINER */
    .highlighted-input-box {
        background: #ffffff;
        border: 2px solid #2563eb;
        border-radius: 14px;
        padding: 18px 20px 14px 20px;
        margin-bottom: 16px;
        box-shadow: 0 6px 20px rgba(37, 99, 235, 0.08);
    }
    .input-label-highlight {
        font-size: 16px;
        font-weight: 800;
        color: #0f172a;
        margin-bottom: 10px;
        display: flex;
        align-items: center;
        gap: 8px;
    }

    /* Highlighting text input with soft tint and blinking cursor */
    .stTextInput > div > div > input {
        background-color: #f8faff !important;
        border: 1.5px solid #3b82f6 !important;
        border-radius: 8px !important;
        font-size: 15px !important;
        color: #0f172a !important;
        caret-color: #1d4ed8 !important;
        padding: 10px 14px !important;
        box-shadow: inset 0 1px 3px rgba(0, 0, 0, 0.04);
    }
    .stTextInput > div > div > input:focus {
        border-color: #1d4ed8 !important;
        background-color: #ffffff !important;
        box-shadow: 0 0 0 3px rgba(37, 99, 235, 0.15) !important;
    }

    /* COMPACT COLORFUL STATUS TILES (Reduced Size, No Arrows) */
    .compact-tile {
        border-radius: 8px;
        padding: 8px 10px;
        text-align: center;
        height: 100%;
        display: flex;
        align-items: center;
        justify-content: center;
        gap: 8px;
        box-shadow: 0 1px 4px rgba(0, 0, 0, 0.04);
        margin-top: 14px;
        margin-bottom: 14px;
    }
    .tile-icon {
        font-size: 16px;
        line-height: 1;
    }
    .tile-text-wrap {
        text-align: left;
    }
    .tile-title {
        font-size: 11px;
        font-weight: 800;
        line-height: 1.2;
    }
    .tile-desc {
        font-size: 9px;
        font-weight: 600;
        line-height: 1.1;
    }

    /* Color variations */
    .tile-blue { background: #e0f2fe; border: 1px solid #bae6fd; color: #0369a1; }
    .tile-blue .tile-desc { color: #0284c7; }

    .tile-green { background: #dcfce7; border: 1px solid #bbf7d0; color: #15803d; }
    .tile-green .tile-desc { color: #16a34a; }

    .tile-orange { background: #ffedd5; border: 1px solid #fed7aa; color: #c2410c; }
    .tile-orange .tile-desc { color: #ea580c; }

    .tile-purple { background: #f3e8ff; border: 1px solid #e9d5ff; color: #7e22ce; }
    .tile-purple .tile-desc { color: #9333ea; }

    .tile-teal { background: #ccfbf1; border: 1px solid #99f6e4; color: #0f766e; }
    .tile-teal .tile-desc { color: #0d9488; }

    /* Footer */
    .omni-footer {
        background: #02163b;
        color: #ffd54f;
        text-align: center;
        padding: 8px;
        border-radius: 6px;
        font-style: italic;
        font-size: 13px;
        letter-spacing: 0.8px;
        margin-top: 20px;
    }
    </style>
    """,
    unsafe_allow_html=True,
)

# 1. Header: PDF Extractor (Golden & White)
st.markdown(
    """
    <div class="system-header-card">
        <div class="system-header-left">
            <div class="system-header-icon">🎓</div>
            <div>
                <div class="system-title" style="color: #ffd700 !important; -webkit-text-fill-color: #ffd700 !important; font-size: 30px !important; font-weight: 800 !important; font-family: 'Cinzel', 'Plus Jakarta Sans', serif, sans-serif !important; letter-spacing: 1px !important; text-shadow: 0 2px 10px rgba(0,0,0,0.5) !important;">PDF Extractor</div>
                <div class="system-subtitle" style="color: #ffffff !important; font-size: 13px !important; font-weight: 500 !important; margin-top: 4px !important;">Universal Document Harvesting • Live Streaming • Rich Metadata Parser</div>
            </div>
        </div>
        <div class="system-badge-right">
            ⚡ Ready
        </div>
    </div>
    """,
    unsafe_allow_html=True,
)

# 2. PROMINENTLY HIGHLIGHTED SEARCH & SETTINGS BOX
with st.container():
    st.markdown('<div class="highlighted-input-box">', unsafe_allow_html=True)
    st.markdown('<div class="input-label-highlight"><span>🔗 Paste Repository, Archive, or Webpage URL:</span></div>', unsafe_allow_html=True)

    url_col, btn_col = st.columns([4, 1])
    with url_col:
        target_url = st.text_input(
            "Target URL",
            placeholder="",
            label_visibility="collapsed",
        )
    with btn_col:
        start_btn = st.button("🚀 Start Extraction", type="primary", use_container_width=True)

    # Inline Settings directly inside the white highlighted box
    with st.expander("⚙️ Crawler Settings", expanded=False):
        scol1, scol2, scol3 = st.columns([2, 1, 1])
        with scol1:
            crawl_mode = st.radio(
                "Crawl Mode",
                options=["Deep Crawl (Follow sublinks)", "Current Page Only"],
                index=0,  # Deep Crawl is default
                horizontal=True,
            )
        with scol2:
            max_pages = st.number_input("Maximum Pages", min_value=1, max_value=500, value=150)
        with scol3:
            request_delay = st.slider("Delay (seconds)", min_value=0.1, max_value=2.0, value=0.5, step=0.1)

    max_depth = 5 if crawl_mode == "Deep Crawl (Follow sublinks)" else 0
    st.markdown('</div>', unsafe_allow_html=True)

# Initialize persistent session state for extraction results
if "raw_harvest" not in st.session_state:
    st.session_state["raw_harvest"] = None
if "session_temp_dir" not in st.session_state:
    st.session_state["session_temp_dir"] = None
if "selected_filenames" not in st.session_state:
    st.session_state["selected_filenames"] = {}
if "bundle_folder_name" not in st.session_state:
    st.session_state["bundle_folder_name"] = "harvested_pdfs"
if "editor_version" not in st.session_state:
    st.session_state["editor_version"] = 0

# 3. EXTRACTION ENGINE TRIGGER
if start_btn:
    if not target_url.strip():
        st.warning("Please enter a valid URL.")
    else:
        url = target_url.strip().strip("'\"")
        if not urlparse(url).scheme:
            url = "https://" + url

        # Clean up old session temp directory if any
        if st.session_state.get("session_temp_dir"):
            shutil.rmtree(st.session_state["session_temp_dir"], ignore_errors=True)
        temp_dir = Path(tempfile.mkdtemp(prefix="pdf_harvest_"))
        st.session_state["session_temp_dir"] = str(temp_dir)

        status_box = st.status("🔍 Initializing extraction engine...", expanded=True)
        downloader = WebDownloader(
            start_url=url,
            delay=request_delay,
            max_pages=max_pages,
            max_depth=max_depth,
            status_container=status_box,
        )
        downloader.temp_dir = temp_dir

        progress_bar = st.progress(0.0)
        downloader.crawl(progress_bar=progress_bar)
        progress_bar.progress(1.0)
        status_box.update(label="✅ Extraction & Metadata Parsing Complete!", state="complete", expanded=False)

        downloaded_count = sum(1 for r in downloader.records if r.status == "Downloaded")
        failed_count = sum(1 for r in downloader.records if r.status == "Failed")

        # Suggest default folder name based on URL path or fallback
        path_name = PurePosixPath(urlparse(url).path).stem
        default_folder = safe_folder_name(path_name) if path_name and len(path_name) > 3 else "harvested_pdfs"
        st.session_state["bundle_folder_name"] = default_folder

        # Initialize all downloaded files to Keep = True
        st.session_state["selected_filenames"] = {
            f: True for f, _, _ in downloader.downloaded_files
        }
        st.session_state["editor_version"] = 0

        # Save harvest records in session_state
        st.session_state["raw_harvest"] = {
            "visited_count": len(downloader.visited),
            "downloaded_count": downloaded_count,
            "failed_count": failed_count,
            "downloaded_files": downloader.downloaded_files,
            "records": downloader.records,
        }

# 4. PERSISTENT RESULTS & SELECTION CONTROLS (Survives button clicks and app reruns)
if st.session_state.get("raw_harvest"):
    temp_dir_str = st.session_state.get("session_temp_dir")
    # If container rebooted and wiped /tmp, reset stale session gracefully without crashing
    if not temp_dir_str or not Path(temp_dir_str).exists():
        st.session_state["raw_harvest"] = None
        st.session_state["session_temp_dir"] = None
        st.session_state["cached_zip_key"] = None
        st.rerun()
    harvest = st.session_state["raw_harvest"]
    downloaded_count = harvest["downloaded_count"]
    failed_count = harvest["failed_count"]
    visited_count = harvest["visited_count"]
    downloaded_files = harvest["downloaded_files"]
    records = harvest["records"]

    # Metric KPI Cards
    mcol1, mcol2, mcol3 = st.columns(3)
    with mcol1:
        st.markdown(
            f"""
            <div style="background: #e0f2fe; border-radius: 10px; padding: 12px; border-left: 5px solid #0284c7;">
                <div style="font-size: 11px; font-weight: 700; color: #0369a1;">PAGES EXPLORED</div>
                <div style="font-size: 24px; font-weight: 800; color: #0c4a6e;">{visited_count}</div>
            </div>
            """,
            unsafe_allow_html=True,
        )
    with mcol2:
        st.markdown(
            f"""
            <div style="background: #dcfce7; border-radius: 10px; padding: 12px; border-left: 5px solid #16a34a;">
                <div style="font-size: 11px; font-weight: 700; color: #15803d;">PDFs HARVESTED</div>
                <div style="font-size: 24px; font-weight: 800; color: #14532d;">{downloaded_count}</div>
            </div>
            """,
            unsafe_allow_html=True,
        )
    with mcol3:
        st.markdown(
            f"""
            <div style="background: #fee2e2; border-radius: 10px; padding: 12px; border-left: 5px solid #dc2626;">
                <div style="font-size: 11px; font-weight: 700; color: #b91c1c;">DOWNLOAD ERRORS</div>
                <div style="font-size: 24px; font-weight: 800; color: #991b1b;">{failed_count}</div>
            </div>
            """,
            unsafe_allow_html=True,
        )

    st.write("")

    if downloaded_count > 0:
        st.markdown("### 📦 Bundle Customization & Document Selection")

        # 1. Ask for folder name after execution
        f_col1, f_col2 = st.columns([2, 1])
        with f_col1:
            custom_folder = st.text_input(
                "📁 Custom Folder & Archive Name:",
                value=st.session_state.get("bundle_folder_name", "harvested_pdfs"),
                help="Name of the exported ZIP and root directory containing your PDFs and metadata.csv",
                key="input_bundle_name",
            )
            st.session_state["bundle_folder_name"] = custom_folder
        with f_col2:
            clean_name = safe_folder_name(custom_folder)
            st.caption("Archive Layout Preview:")
            st.code(f"{clean_name}.zip\n  ├── {clean_name}/PDFs/...\n  └── {clean_name}/metadata.csv", language="text")

        # 2. Select All / Deselect All controls
        sel_col1, sel_col2, sel_col3 = st.columns([1, 1, 2])
        with sel_col1:
            if st.button("✅ Select All", use_container_width=True):
                for f, _, _ in downloaded_files:
                    st.session_state["selected_filenames"][f] = True
                st.session_state["editor_version"] = st.session_state.get("editor_version", 0) + 1
                st.rerun()
        with sel_col2:
            if st.button("❌ Deselect All", use_container_width=True):
                for f, _, _ in downloaded_files:
                    st.session_state["selected_filenames"][f] = False
                st.session_state["editor_version"] = st.session_state.get("editor_version", 0) + 1
                st.rerun()

        # Prepare DataFrame for interactive keep/ignore selection
        doc_list = []
        for rec in records:
            if rec.status == "Downloaded":
                is_kept = st.session_state["selected_filenames"].get(rec.filename, True)
                doc_list.append({
                    "Keep": is_kept,
                    "Document Title": rec.title,
                    "File Name": rec.filename,
                    "Size (KB)": round(rec.size_bytes / 1024, 1),
                    "Issue Date": rec.date or "—",
                    "Publisher / Source": rec.publisher or "—",
                })

        editor_key = f"manifest_editor_{st.session_state.get('editor_version', 0)}"
        table_data = pd.DataFrame(doc_list) if HAS_PANDAS else doc_list
        edited_df = st.data_editor(
            table_data,
            column_config={
                "Keep": st.column_config.CheckboxColumn("Keep", default=True, help="Check to include in ZIP bundle"),
            },
            disabled=["Document Title", "File Name", "Size (KB)", "Issue Date", "Publisher / Source"],
            hide_index=True,
            use_container_width=True,
            key=editor_key,
        )

        # Sync user checkbox edits back to session state safely
        if HAS_PANDAS and hasattr(edited_df, "to_dict"):
            table_rows = edited_df.to_dict(orient="records")
        elif isinstance(edited_df, list):
            table_rows = edited_df
        else:
            table_rows = doc_list

        kept_filenames = {r["File Name"] for r in table_rows if r.get("Keep", True)}
        for f, _, _ in downloaded_files:
            st.session_state["selected_filenames"][f] = (f in kept_filenames)

        # Filter selected files & records
        selected_files = [f for f in downloaded_files if f[0] in kept_filenames]
        selected_records = [r for r in records if r.filename in kept_filenames]

        with sel_col3:
            total_kb = sum(r.size_bytes for r in selected_records) / 1024
            size_str = f"{round(total_kb / 1024, 2)} MB" if total_kb >= 1024 else f"{round(total_kb, 1)} KB"
            st.markdown(f"<div style='padding-top: 6px; font-weight: 700; color: #1e40af;'>📌 Selected: {len(selected_files)} of {downloaded_count} documents ({size_str})</div>", unsafe_allow_html=True)

        st.write("")

        # 3. Stream ZIP directly from disk without consuming RAM
        if selected_files:
            cache_key = (clean_name, tuple(sorted(kept_filenames)))
            zip_file_path = Path(st.session_state["session_temp_dir"]) / f"{clean_name}.zip"

            # Rebuild on disk ONLY if the selection or folder name changed
            if st.session_state.get("cached_zip_key") != cache_key or not zip_file_path.exists():
                build_zip_on_disk(selected_files, selected_records, zip_file_path, folder_name=clean_name)
                st.session_state["cached_zip_key"] = cache_key
                gc.collect()

            # Stream directly from disk using file binary reader
            with open(zip_file_path, "rb") as zip_stream:
                st.download_button(
                    label=f"📥 Download {len(selected_files)} Selected PDFs + Metadata (ZIP • {size_str})",
                    data=zip_stream,
                    file_name=f"{clean_name}.zip",
                    mime="application/zip",
                    type="primary",
                    use_container_width=True,
                    key="download_harvested_zip_btn",
                )
        else:
            st.warning("⚠️ No documents selected. Please check at least one document to enable ZIP download.")
    else:
        st.info("No PDF documents were found at the provided URL.")
# 5. COMPACT 5 SMALL COLORFUL BOXES (Placed below the search and result area)
tcol1, tcol2, tcol3, tcol4, tcol5 = st.columns(5)
with tcol1:
    st.markdown(
        """
        <div class="compact-tile tile-blue">
            <span class="tile-icon">🌐</span>
            <div class="tile-text-wrap">
                <div class="tile-title">Auto Engine</div>
                <div class="tile-desc">DSpace / Web</div>
            </div>
        </div>
        """,
        unsafe_allow_html=True,
    )
with tcol2:
    st.markdown(
        """
        <div class="compact-tile tile-green">
            <span class="tile-icon">🌿</span>
            <div class="tile-text-wrap">
                <div class="tile-title">Deep Crawl</div>
                <div class="tile-desc">Sublink Recursion</div>
            </div>
        </div>
        """,
        unsafe_allow_html=True,
    )
with tcol3:
    st.markdown(
        """
        <div class="compact-tile tile-orange">
            <span class="tile-icon">⚡</span>
            <div class="tile-text-wrap">
                <div class="tile-title">Live Stream</div>
                <div class="tile-desc">Memory Safe</div>
            </div>
        </div>
        """,
        unsafe_allow_html=True,
    )
with tcol4:
    st.markdown(
        """
        <div class="compact-tile tile-purple">
            <span class="tile-icon">📚</span>
            <div class="tile-text-wrap">
                <div class="tile-title">Metadata</div>
                <div class="tile-desc">Title • Author • Date</div>
            </div>
        </div>
        """,
        unsafe_allow_html=True,
    )
with tcol5:
    st.markdown(
        """
        <div class="compact-tile tile-teal">
            <span class="tile-icon">📦</span>
            <div class="tile-text-wrap">
                <div class="tile-title">ZIP Export</div>
                <div class="tile-desc">1-Click Bundle</div>
            </div>
        </div>
        """,
        unsafe_allow_html=True,
    )

# 5. Footer Banner
st.markdown(
    """
    <div class="omni-footer">
        Knowledge Today... Success Tomorrow...
    </div>
    """,
    unsafe_allow_html=True,
)
