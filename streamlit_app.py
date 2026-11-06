#!/usr/bin/env python3
"""
Universal PDF Harvester - Streamlit Web & CLI Application
---------------------------------------------------------
A unified, resilient document harvesting engine designed for:
1. Academic Repositories (DSpace, eGyanKosh, NDLI - Community, Collection, and Unit Items)
2. Government Document & PYQ Portals (WBJEEB, S3WaaS, NIC, NTA tables & pagination)
3. State Commission Archives (WBCSC SET Question Papers - ASP.NET WebForms postbacks)
4. Generic Educational & Resource Pages (Direct PDFs, syllabus links, tables)

Features:
- Dual-Mode: Interactive Streamlit Web UI + Pure Command-Line (CLI) Mode
- Memory-Safe: Disk-backed streaming prevents RAM exhaustion on cloud containers
- Automatic Protocol Fallback: Gracefully retries http:// if https:// fails on legacy servers
- Thumbnail Immunity: Rejects image previews (.jpg, .png) and extracts authentic PDF bitstreams
- Full Metadata Extraction: Captures titles, publication dates, authors, and sources
"""

from __future__ import annotations

import csv
import gc
import io
import os
import re
import ssl
import sys
import time
import zipfile
import tempfile
from collections import deque
from dataclasses import dataclass
from html import unescape
from pathlib import Path, PurePosixPath
from urllib.parse import urljoin, urlparse, urldefrag, unquote, urlsplit, urlunsplit

import urllib3
import requests
from bs4 import BeautifulSoup

# Streamlit import with runtime detection
try:
    import streamlit as st
    from streamlit.runtime import exists as st_runtime_exists
    HAS_STREAMLIT = True
    RUNNING_IN_STREAMLIT = st_runtime_exists()
except Exception:
    st = None
    HAS_STREAMLIT = False
    RUNNING_IN_STREAMLIT = False

# Optional pandas support for interactive tables
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

# Suppress insecure SSL warnings for institutional / educational portals
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)


# -------------------------------------------------------------
# Constants & Helper Regexes
# -------------------------------------------------------------

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/128.0.0.0 Safari/537.36"
)

# Standard browser request headers
DEFAULT_HEADERS = {
    "User-Agent": USER_AGENT,
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,application/pdf,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9,hi;q=0.8,bn;q=0.7",
    "Connection": "keep-alive",
    "Sec-Ch-Ua": '"Chromium";v="128", "Not;A=Brand";v="24", "Google Chrome";v="128"',
    "Sec-Ch-Ua-Mobile": "?0",
    "Sec-Ch-Ua-Platform": '"Windows"',
    "Sec-Fetch-Dest": "document",
    "Sec-Fetch-Mode": "navigate",
    "Sec-Fetch-Site": "none",
    "Sec-Fetch-User": "?1",
    "Upgrade-Insecure-Requests": "1",
}

# Regex Patterns
HANDLE_RE = re.compile(r"/handle/(\d+)/([^/?#]+)", re.I)
DSPACE_HANDLE_PATTERN = re.compile(r"^/+handle/(\d+)/([a-zA-Z0-9_.\-]+)$", re.I)
POSTBACK_RE = re.compile(r"__doPostBack\s*\(\s*['\"]([^'\"]+)['\"]\s*,\s*['\"]([^'\"]*)['\"]\s*\)", re.I)
BAD_CHARS = re.compile(r'[<>:"/\\|?*\x00-\x1f]')

WINDOWS_RESERVED = {
    "CON", "PRN", "AUX", "NUL",
    *(f"COM{i}" for i in range(1, 10)),
    *(f"LPT{i}" for i in range(1, 10)),
}

SKIPPABLE_EXTENSIONS = {
    ".png", ".jpg", ".jpeg", ".gif", ".webp", ".svg", ".ico",
    ".css", ".js", ".mp4", ".mp3", ".zip", ".tar", ".gz", ".7z",
    ".exe", ".dmg", ".apk", ".docx", ".xlsx", ".pptx"
}


# -------------------------------------------------------------
# Legacy SSL Adapter (Supports Older Institutional Portals)
# -------------------------------------------------------------

class LegacySSLAdapter(requests.adapters.HTTPAdapter):
    """Permits legacy TLS versions and ciphers used on older Indian university portals."""
    def init_poolmanager(self, *args, **kwargs):
        try:
            from urllib3.util.ssl_ import create_urllib3_context
            ctx = create_urllib3_context()
            ctx.check_hostname = False
            ctx.verify_mode = ssl.CERT_NONE
            try:
                ctx.set_ciphers("DEFAULT@SECLEVEL=1")
            except Exception:
                pass
            kwargs["ssl_context"] = ctx
        except Exception:
            pass
        return super().init_poolmanager(*args, **kwargs)


# -------------------------------------------------------------
# Clean Normalization & Utility Functions
# -------------------------------------------------------------

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


def visited_key(url: str) -> str:
    """Normalizes URL for duplicate prevention across http/https and trailing slashes."""
    u = urlsplit(url)
    netloc = normalize_host(u.netloc)
    path = u.path.rstrip("/")
    while "//" in path:
        path = path.replace("//", "/")
    return f"{netloc}{path}"


def is_pdf_url(url: str) -> bool:
    path = urlparse(url).path.lower()
    return path.endswith(".pdf") or ".pdf?" in url.lower() or "/bitstream/" in path


def is_valid_pdf_bitstream(href: str) -> bool:
    """Rejects DSpace thumbnail image bundles (.jpg, .png) and non-PDF bitstreams."""
    p = urlparse(href).path.lower()
    if any(p.endswith(ext) for ext in (".jpg", ".jpeg", ".png", ".gif", ".webp", ".txt", ".mp4", ".mp3")):
        return False
    if any(ext in href.lower() for ext in (".jpg?", ".jpeg?", ".png?", ".gif?", ".webp?", "thumbnail")):
        return False
    return True


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


def extract_aspnet_form_data(soup: BeautifulSoup) -> dict:
    """Extracts hidden ASP.NET WebForms inputs required for __doPostBack simulation."""
    data = {}
    for inp in soup.find_all("input"):
        name = inp.get("name")
        if not name:
            continue
        val = inp.get("value", "")
        data[name] = val
    return data


# -------------------------------------------------------------
# Data Models
# -------------------------------------------------------------

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
    error: str = ""


# -------------------------------------------------------------
# Core Harvesting Engine
# -------------------------------------------------------------

class WebDownloader:
    def __init__(self, start_url: str, delay: float = 0.5,
                 timeout: int = 35, max_pages: int = 150,
                 max_depth: int = 5, status_container=None):
        self.start_url = canonical(start_url)
        self.host = urlparse(start_url).netloc
        self.delay = delay
        self.timeout = timeout
        self.max_pages = max_pages
        self.max_depth = max_depth
        self.status_container = status_container

        self.session = requests.Session()
        adapter = LegacySSLAdapter()
        self.session.mount("https://", adapter)
        self.session.mount("http://", adapter)
        self.session.headers.update(DEFAULT_HEADERS)

        self.visited = set()
        self.records: list[DownloadRecord] = []
        self.pdf_url_seen = set()
        self.downloaded_files: list[tuple[str, Path, str]] = []
        self.temp_dir: Path | None = None
        self.is_dspace_repo = False

    def log(self, message: str):
        if self.status_container:
            self.status_container.write(message)
        elif not RUNNING_IN_STREAMLIT:
            print("  " + re.sub(r"[*`#_]", "", message))

    def get(self, url: str, stream: bool = False, headers: dict | None = None):
        """HTTP GET with automatic HTTPS -> HTTP fallback for older institutional servers."""
        last_error = None
        req_headers = dict(self.session.headers)
        if headers:
            req_headers.update(headers)

        # Candidate schemes: if https fails/times out, try http port 80 immediately
        targets = [url]
        if url.startswith("https://"):
            targets.append("http://" + url[8:])
        elif url.startswith("http://"):
            targets.append("https://" + url[7:])

        for target in targets:
            for attempt in range(2):
                try:
                    response = self.session.get(
                        target,
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
                    time.sleep(0.4)

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
            v_key = visited_key(url)
            if v_key in self.visited:
                continue
            self.visited.add(v_key)

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

    # ---------------------------------------------------------
    # DSpace Repository Processor (eGyanKosh, NDLI)
    # ---------------------------------------------------------

    def process_dspace(self, soup: BeautifulSoup, page_url: str, queue: deque, depth: int):
        # 1. On starting page, blacklist parent breadcrumbs so crawler only travels downwards into course units
        if depth == 0:
            for b in soup.find_all(["ol", "ul", "div", "nav"], class_=lambda c: c and any(w in str(c).lower() for w in ("breadcrumb", "trail", "breadcrumbs"))):
                for a in b.find_all("a", href=True):
                    self.visited.add(visited_key(urljoin(page_url, a["href"])))

        # 2. Extract direct bitstream PDF links if present (works across both DSpace JSPUI & XMLUI item pages)
        pdf_links = self.extract_dspace_pdf_links(soup, page_url)
        if pdf_links:
            meta = self.extract_dspace_metadata(soup)
            for pdf_url, label in pdf_links:
                raw_name = label or PurePosixPath(urlparse(pdf_url).path).name
                filename = safe_filename(raw_name)
                self.download_pdf(pdf_url, filename, page_url, meta=meta)
            return

        # 3. Community / Collection Index: auto-expand recursion depth to guarantee finding child units
        if depth == 0 and not pdf_links and self.max_depth == 0:
            self.max_depth = 5
            self.log("ℹ️ Index page detected without direct PDFs. Auto-expanding depth to traverse child collections.")

        if depth < self.max_depth:
            search_scope = soup.body or soup
            for a in search_scope.find_all("a", href=True):
                # Skip header, navbar, footer, search facets
                if a.find_parent(["header", "footer", "nav"]) or a.find_parent(
                    class_=lambda c: c and any(w in str(c).lower() for w in ("breadcrumb", "trail", "navbar", "header", "footer", "facet"))
                ):
                    continue

                raw_href = a["href"].strip()
                if any(w in raw_href.lower() for w in ("simple-search", "browse?", "/browse", "login", "register", "password", "signon", "?mode=full")):
                    continue

                child_url = canonical(urljoin(page_url, raw_href))
                u = urlparse(child_url)
                norm_path = "/" + u.path.lstrip("/")

                if same_site(child_url, self.host) and DSPACE_HANDLE_PATTERN.match(norm_path.rstrip("/")):
                    c_key = visited_key(child_url)
                    if c_key not in self.visited and not any(child_url == q_url for q_url, _ in queue):
                        queue.append((child_url, depth + 1))

    def extract_dspace_pdf_links(self, soup: BeautifulSoup, page_url: str):
        found = []
        seen_paths = set()
        generic_labels = {"view", "open", "view/open", "download", "show", "thumbnail", ""}

        # 1. Parse DSpace file tables (JSPUI and XMLUI)
        for table in soup.find_all("table"):
            for row in table.find_all("tr"):
                cells = row.find_all(["td", "th"])

                # Discard image thumbnails (.jpg, .png) and non-PDF bitstreams
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

                # Prioritize direct .pdf links over extensionless bitstream endpoints
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

        # 2. Check for standalone bitstream links outside tables
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

        # Fallback table parser for JSPUI simple item displays
        table = soup.select_one("table.itemDisplayTable")
        if table:
            for row in table.find_all("tr"):
                label_el = row.find(class_="metadataFieldLabel")
                value_el = row.find(class_="metadataFieldValue")
                if label_el and value_el:
                    k = clean_text(label_el.get_text(" ", strip=True)).rstrip(":")
                    v = clean_text(value_el.get_text(" ", strip=True))
                    if k and v:
                        data.setdefault(k, []).append(v)

        def get_meta_field(*names):
            for name in names:
                for k, vals in data.items():
                    if k.lower() == name.lower():
                        return "; ".join(vals)
            return ""

        return {
            "title": get_meta_field("dc.title", "citation_title", "title"),
            "authors": get_meta_field("dc.contributor.author", "dc.creator", "citation_authors", "authors", "author"),
            "date": get_meta_field("dc.date.issued", "dcterms.issued", "dc.date", "citation_date", "date", "issue date"),
            "publisher": get_meta_field("dc.publisher", "citation_publisher", "publisher"),
            "subject": get_meta_field("dc.subject", "keywords", "subject"),
            "description": get_meta_field("dc.description.abstract", "dc.description", "description"),
            "language": get_meta_field("dc.language", "dc.language.iso", "language"),
        }

    # ---------------------------------------------------------
    # Document Portals, S3WaaS (WBJEEB) & General Webpages
    # ---------------------------------------------------------

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

        # 1. Parse structured tables (e.g., WBJEEB S3WaaS: Title | Session | View/Download)
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

                        # ASP.NET WebForms __doPostBack LinkButtons (e.g. WBCSC SET Question Papers)
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

        # 2. Parse direct PDF links outside tables
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

        # 3. Follow subpages & pagination within depth limit
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
                c_key = visited_key(href)
                if c_key not in self.visited and not any(href == q_url for q_url, _ in queue):
                    queue.append((href, depth + 1))

        # 4. Auto-explore ASP.NET dropdown menus if present
        if page_url.lower().endswith(".aspx") or soup.find("input", attrs={"name": "__VIEWSTATE"}):
            self.process_aspnet_dropdowns(soup, page_url, queue, depth)

    # ---------------------------------------------------------
    # ASP.NET WebForms Engine (WBCSC SET Question Papers)
    # ---------------------------------------------------------

    def download_aspnet_postback(self, page_url: str, soup: BeautifulSoup, target: str, argument: str,
                                 base_filename: str, meta: dict | None = None, page_title: str = ""):
        post_key = f"{page_url}#__postback__{target}__{argument}"
        if post_key in self.pdf_url_seen:
            return
        self.pdf_url_seen.add(post_key)

        data = extract_aspnet_form_data(soup)
        data["__EVENTTARGET"] = target
        data["__EVENTARGUMENT"] = argument

        stem = base_filename[:-4] if base_filename.lower().endswith(".pdf") else base_filename
        target_path = self.temp_dir / base_filename
        counter = 2
        existing_names = {f for f, _, _ in self.downloaded_files}
        while target_path.exists() or target_path.name in existing_names:
            target_path = self.temp_dir / f"{stem}_{counter}.pdf"
            counter += 1

        filename = target_path.name
        self.log(f"⬇️ PostBack Downloading: **{filename}**")

        try:
            if self.delay:
                time.sleep(self.delay)

            headers = {"Referer": page_url, "Content-Type": "application/x-www-form-urlencoded"}
            response = self.session.post(
                page_url,
                data=data,
                headers=headers,
                timeout=self.timeout,
                stream=True,
                allow_redirects=True,
                verify=False,
            )
            response.raise_for_status()

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

            if b"%PDF-" not in signature:
                target_path.unlink(missing_ok=True)
                raise ValueError("PostBack response was not a valid PDF")

            pdf_internal_meta = extract_pdf_file_metadata(target_path)
            meta = dict(meta or {})
            if pdf_internal_meta.get("authors") and not meta.get("authors"):
                meta["authors"] = pdf_internal_meta["authors"]
            if pdf_internal_meta.get("date") and not meta.get("date"):
                meta["date"] = pdf_internal_meta["date"]

            record = DownloadRecord(
                title=meta.get("title") or page_title or filename[:-4],
                authors=meta.get("authors", ""),
                date=meta.get("date", ""),
                publisher=meta.get("publisher", ""),
                subject=meta.get("subject", ""),
                description=meta.get("description", ""),
                language=meta.get("language", ""),
                item_type="PDF Document",
                page_url=page_url,
                pdf_url=post_key,
                filename=filename,
                size_bytes=total,
                status="Downloaded",
            )
            self.records.append(record)
            self.downloaded_files.append((filename, target_path, page_url))
            self.log(f"✅ Harvested `{filename}` ({round(total / 1024, 1)} KB)")

        except Exception as exc:
            self.records.append(DownloadRecord(
                title=meta.get("title") or page_title or filename[:-4],
                authors=meta.get("authors", ""),
                date=meta.get("date", ""),
                publisher=meta.get("publisher", ""),
                subject=meta.get("subject", ""),
                description=meta.get("description", ""),
                language=meta.get("language", ""),
                item_type="PDF Document",
                page_url=page_url,
                pdf_url=post_key,
                filename=filename,
                size_bytes=0,
                status="Failed",
                error=str(exc),
            ))
            self.log(f"❌ Failed PostBack `{filename}`: {exc}")

    def process_aspnet_dropdowns(self, soup: BeautifulSoup, page_url: str, queue: deque, depth: int):
        form_data = extract_aspnet_form_data(soup)
        for select in soup.find_all("select"):
            select_name = select.get("name")
            if not select_name or select_name.startswith("__"):
                continue

            options = select.find_all("option")
            for opt in options:
                val = opt.get("value")
                opt_text = clean_text(opt.get_text(" ", strip=True))
                if not val or val in ("0", "-1", "", "Select"):
                    continue

                session_key = f"{page_url}#{select_name}={val}"
                if visited_key(session_key) in self.visited:
                    continue
                self.visited.add(visited_key(session_key))

                sub_data = dict(form_data)
                sub_data[select_name] = val
                sub_data["__EVENTTARGET"] = select_name
                sub_data["__EVENTARGUMENT"] = ""

                try:
                    self.log(f"🔄 Exploring Dropdown: `{select_name}` = **{opt_text}**")
                    if self.delay:
                        time.sleep(self.delay)

                    res = self.session.post(
                        page_url,
                        data=sub_data,
                        headers={"Referer": page_url, "Content-Type": "application/x-www-form-urlencoded"},
                        timeout=self.timeout,
                        verify=False,
                    )
                    res.raise_for_status()

                    sub_soup = BeautifulSoup(res.text, "html.parser")
                    self.process_generic(sub_soup, page_url, queue, depth + 1)
                    del sub_soup
                    res.close()
                    del res
                    gc.collect()
                except Exception as exc:
                    self.log(f"⚠️ Could not load dropdown `{opt_text}`: {exc}")

    # ---------------------------------------------------------
    # PDF Binary Downloader with Chunk Verification
    # ---------------------------------------------------------

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
            if pdf_internal_meta.get("authors") and not meta.get("authors"):
                meta["authors"] = pdf_internal_meta["authors"]
            if pdf_internal_meta.get("date") and not meta.get("date"):
                meta["date"] = pdf_internal_meta["date"]

            record = DownloadRecord(
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
                size_bytes=total,
                status="Downloaded",
            )
            self.records.append(record)
            self.downloaded_files.append((filename, target_path, page_url))
            self.log(f"✅ Harvested `{filename}` ({round(total / 1024, 1)} KB)")

        except Exception as exc:
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


# -------------------------------------------------------------
# Disk-Backed Streaming ZIP Packaging (Zero RAM Impact)
# -------------------------------------------------------------

def build_zip_on_disk(downloaded_files, records, output_zip_path: Path, folder_name: str = "harvested_pdfs") -> None:
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
# Streamlit Web UI Mode
# -------------------------------------------------------------

def render_streamlit_ui():
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

    # Custom Golden & Navy Styling
    st.markdown(
        """
        <style>
        @import url('https://fonts.googleapis.com/css2?family=Plus+Jakarta+Sans:wght@400;500;600;700;800&family=Cinzel:wght@700;800&display=swap');

        .stApp {
            background: #f4f7fb;
            font-family: 'Plus Jakarta Sans', sans-serif;
        }

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
            gap: 16px;
        }
        .system-header-logo {
            font-size: 38px;
            background: rgba(255, 255, 255, 0.08);
            border: 1px solid rgba(212, 175, 55, 0.4);
            border-radius: 12px;
            width: 56px;
            height: 56px;
            display: flex;
            align-items: center;
            justify-content: center;
        }
        .system-header-titles {
            display: flex;
            flex-direction: column;
        }
        .system-header-title {
            font-family: 'Cinzel', serif !important;
            color: #ffd700 !important;
            font-size: 26px !important;
            font-weight: 800 !important;
            letter-spacing: 1.2px;
            margin: 0;
            line-height: 1.1;
            text-shadow: 0 2px 4px rgba(0, 0, 0, 0.4);
        }
        .system-header-subtitle {
            font-size: 13px;
            color: #ffffff !important;
            font-weight: 500;
            letter-spacing: 0.4px;
            margin-top: 4px;
        }
        .system-header-badge {
            background: rgba(212, 175, 55, 0.15);
            border: 1px solid #d4af37;
            color: #ffd700;
            padding: 6px 14px;
            border-radius: 20px;
            font-size: 11px;
            font-weight: 700;
            letter-spacing: 0.8px;
            text-transform: uppercase;
        }

        .highlight-input-box {
            background: #ffffff;
            border-radius: 14px;
            padding: 22px 24px;
            border: 1px solid #e2e8f0;
            box-shadow: 0 4px 14px rgba(0, 0, 0, 0.04);
            margin-bottom: 20px;
        }

        .compact-tile {
            background: #ffffff;
            border: 1px solid #e2e8f0;
            border-radius: 10px;
            padding: 10px 14px;
            display: flex;
            align-items: center;
            gap: 10px;
            box-shadow: 0 2px 6px rgba(0, 0, 0, 0.03);
            margin-bottom: 8px;
        }
        .compact-tile .tile-icon {
            font-size: 20px;
            width: 32px;
            height: 32px;
            display: flex;
            align-items: center;
            justify-content: center;
            border-radius: 8px;
        }
        .tile-blue .tile-icon { background: #eff6ff; color: #1d4ed8; }
        .tile-green .tile-icon { background: #f0fdf4; color: #15803d; }
        .tile-orange .tile-icon { background: #fff7ed; color: #c2410c; }
        .tile-purple .tile-icon { background: #faf5ff; color: #7e22ce; }
        .tile-teal .tile-icon { background: #f0fdfa; color: #0f766e; }

        .tile-text-wrap {
            display: flex;
            flex-direction: column;
            line-height: 1.2;
        }
        .tile-title {
            font-size: 12px;
            font-weight: 700;
            color: #0f172a !important;
        }
        .tile-desc {
            font-size: 10px;
            color: #64748b !important;
            font-weight: 500;
        }

        .footer-banner {
            text-align: center;
            padding: 18px;
            margin-top: 24px;
            color: #64748b;
            font-size: 12px;
            border-top: 1px solid #e2e8f0;
        }
        .footer-motto {
            font-family: 'Cinzel', serif;
            font-weight: 700;
            color: #1e3a8a;
            letter-spacing: 1px;
            font-size: 14px;
        }
        </style>
        """,
        unsafe_allow_html=True,
    )

    # 1. Header Card
    st.markdown(
        """
        <div class="system-header-card">
            <div class="system-header-left">
                <div class="system-header-logo">🎓</div>
                <div class="system-header-titles">
                    <div class="system-header-title">UNIVERSAL PDF HARVESTER</div>
                    <div class="system-header-subtitle">Bulk Document Extractor for Repositories, Portals & PYQ Archives</div>
                </div>
            </div>
            <div class="system-header-badge">Production v3.2</div>
        </div>
        """,
        unsafe_allow_html=True,
    )

    # Self-healing Session State
    if "session_temp_dir" in st.session_state and st.session_state["session_temp_dir"]:
        if not Path(st.session_state["session_temp_dir"]).exists():
            st.session_state["raw_harvest"] = None
            st.session_state["session_temp_dir"] = None
            st.session_state["selected_filenames"] = {}
            st.session_state["editor_version"] = 0
            st.session_state["cached_zip_key"] = None

    # 2. Input Box & Settings
    st.markdown('<div class="highlight-input-box">', unsafe_allow_html=True)
    url_col, btn_col = st.columns([4, 1])

    with url_col:
        target_url = st.text_input(
            "Target Repository / Portal URL:",
            placeholder="e.g. https://wbjeeb.nic.in/old-question-paper-wbjee/ or http://egyankosh.ac.in/handle/123456789/70823",
            help="Paste any DSpace URL (eGyanKosh, NDLI), S3WaaS Exam Portal (WBJEEB), or State Commission Archive (WBCSC).",
            label_visibility="collapsed",
        )

    with btn_col:
        start_btn = st.button("🚀 Start Harvesting", type="primary", use_container_width=True)

    with st.expander("⚙️ Crawler Settings", expanded=False):
        scol1, scol2, scol3 = st.columns([2, 1, 1])
        with scol1:
            crawl_mode = st.radio(
                "Crawl Mode",
                options=["Deep Crawl (Follow sublinks)", "Current Page Only"],
                index=0,
                horizontal=True,
            )
        with scol2:
            max_pages = st.number_input("Maximum Pages", min_value=1, max_value=500, value=150)
        with scol3:
            request_delay = st.slider("Delay (seconds)", min_value=0.1, max_value=2.0, value=0.5, step=0.1)

    max_depth = 5 if crawl_mode == "Deep Crawl (Follow sublinks)" else 0
    st.markdown('</div>', unsafe_allow_html=True)

    # Initialize persistent state
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

    # 3. Trigger Crawl
    if start_btn:
        if not target_url.strip():
            st.warning("Please enter a valid URL.")
        else:
            url = target_url.strip().strip("'\"")
            if not urlparse(url).scheme:
                url = "https://" + url

            temp_dir = Path(tempfile.mkdtemp(prefix="harvest_"))
            st.session_state["session_temp_dir"] = str(temp_dir)
            st.session_state["cached_zip_key"] = None

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

            path_name = PurePosixPath(urlparse(url).path).stem
            default_folder = safe_folder_name(path_name) if path_name and len(path_name) > 3 else "harvested_pdfs"
            st.session_state["bundle_folder_name"] = default_folder

            st.session_state["selected_filenames"] = {
                f: True for f, _, _ in downloader.downloaded_files
            }
            st.session_state["editor_version"] = 0

            st.session_state["raw_harvest"] = {
                "visited_count": len(downloader.visited),
                "downloaded_count": downloaded_count,
                "failed_count": failed_count,
                "downloaded_files": downloader.downloaded_files,
                "records": downloader.records,
            }

    # 4. Results & Selection Dashboard
    if st.session_state.get("raw_harvest"):
        harvest_data = st.session_state["raw_harvest"]
        downloaded_count = harvest_data["downloaded_count"]
        failed_count = harvest_data["failed_count"]
        visited_count = harvest_data["visited_count"]
        downloaded_files = harvest_data["downloaded_files"]
        records = harvest_data["records"]

        # Summary Metric Tiles
        m1, m2, m3, m4 = st.columns(4)
        with m1:
            st.markdown(
                f"""
                <div style="background: #ffffff; border-radius: 10px; padding: 12px; border-left: 5px solid #2563eb; box-shadow: 0 2px 4px rgba(0,0,0,0.04);">
                    <div style="font-size: 11px; font-weight: 700; color: #64748b;">PAGES CRAWLED</div>
                    <div style="font-size: 24px; font-weight: 800; color: #1e3a8a;">{visited_count}</div>
                </div>
                """,
                unsafe_allow_html=True,
            )
        with m2:
            st.markdown(
                f"""
                <div style="background: #ffffff; border-radius: 10px; padding: 12px; border-left: 5px solid #16a34a; box-shadow: 0 2px 4px rgba(0,0,0,0.04);">
                    <div style="font-size: 11px; font-weight: 700; color: #64748b;">PDFS HARVESTED</div>
                    <div style="font-size: 24px; font-weight: 800; color: #15803d;">{downloaded_count}</div>
                </div>
                """,
                unsafe_allow_html=True,
            )
        with m3:
            total_bytes = sum(r.size_bytes for r in records if r.status == "Downloaded")
            size_mb = round(total_bytes / (1024 * 1024), 2)
            st.markdown(
                f"""
                <div style="background: #ffffff; border-radius: 10px; padding: 12px; border-left: 5px solid #d97706; box-shadow: 0 2px 4px rgba(0,0,0,0.04);">
                    <div style="font-size: 11px; font-weight: 700; color: #64748b;">TOTAL HARVEST SIZE</div>
                    <div style="font-size: 24px; font-weight: 800; color: #b45309;">{size_mb} MB</div>
                </div>
                """,
                unsafe_allow_html=True,
            )
        with m4:
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

            doc_list = []
            for rec in records:
                if rec.status == "Downloaded":
                    is_kept = st.session_state["selected_filenames"].get(rec.filename, True)
                    doc_list.append({
                        "Keep": is_kept,
                        "Document Title": rec.title,
                        "Date / Session": rec.date,
                        "Authors / Publisher": rec.authors or rec.publisher,
                        "File Name": rec.filename,
                        "Size (KB)": round(rec.size_bytes / 1024, 1),
                    })

            editor_key = f"doc_editor_{st.session_state.get('editor_version', 0)}"
            if HAS_PANDAS:
                df = pd.DataFrame(doc_list)
                edited_df = st.data_editor(
                    df,
                    column_config={"Keep": st.column_config.CheckboxColumn("Keep", help="Include in ZIP", default=True)},
                    disabled=["Document Title", "Date / Session", "Authors / Publisher", "File Name", "Size (KB)"],
                    hide_index=True,
                    use_container_width=True,
                    key=editor_key,
                )
                table_rows = edited_df.to_dict(orient="records")
            else:
                table_rows = doc_list

            kept_filenames = {r["File Name"] for r in table_rows if r.get("Keep", True)}
            for f, _, _ in downloaded_files:
                st.session_state["selected_filenames"][f] = (f in kept_filenames)

            selected_files = [f for f in downloaded_files if f[0] in kept_filenames]
            selected_records = [r for r in records if r.filename in kept_filenames]

            with sel_col3:
                total_kb = sum(r.size_bytes for r in selected_records) / 1024
                size_str = f"{round(total_kb / 1024, 2)} MB" if total_kb >= 1024 else f"{round(total_kb, 1)} KB"
                st.markdown(f"<div style='padding-top: 6px; font-weight: 700; color: #1e40af;'>📌 Selected: {len(selected_files)} of {downloaded_count} documents ({size_str})</div>", unsafe_allow_html=True)

            st.write("")

            # Zero-RAM Disk Streaming
            if selected_files:
                cache_key = (clean_name, tuple(sorted(kept_filenames)))
                zip_file_path = Path(st.session_state["session_temp_dir"]) / f"{clean_name}.zip"

                if st.session_state.get("cached_zip_key") != cache_key or not zip_file_path.exists():
                    build_zip_on_disk(selected_files, selected_records, zip_file_path, folder_name=clean_name)
                    st.session_state["cached_zip_key"] = cache_key
                    gc.collect()

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

    # 5. Bottom Status Tiles
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
                <span class="tile-icon">🛡️</span>
                <div class="tile-text-wrap">
                    <div class="tile-title">Duplicate Shield</div>
                    <div class="tile-desc">Zero Redundancy</div>
                </div>
            </div>
            """,
            unsafe_allow_html=True,
        )
    with tcol4:
        st.markdown(
            """
            <div class="compact-tile tile-purple">
                <span class="tile-icon">⚡</span>
                <div class="tile-text-wrap">
                    <div class="tile-title">Direct Stream</div>
                    <div class="tile-desc">Zero-RAM Writes</div>
                </div>
            </div>
            """,
            unsafe_allow_html=True,
        )
    with tcol5:
        st.markdown(
            """
            <div class="compact-tile tile-teal">
                <span class="tile-icon">🧹</span>
                <div class="tile-text-wrap">
                    <div class="tile-title">Auto Clean</div>
                    <div class="tile-desc">Clean Naming</div>
                </div>
            </div>
            """,
            unsafe_allow_html=True,
        )

    # Footer
    st.markdown(
        """
        <div class="footer-banner">
            <span class="footer-motto">"Knowledge Today... Success Tomorrow..."</span><br>
            Universal Educational Document & Examination PYQ Extraction System • Designed for High-Volume Academic Harvesting
        </div>
        """,
        unsafe_allow_html=True,
    )


# -------------------------------------------------------------
# Command-Line (CLI) Mode
# -------------------------------------------------------------

def run_cli():
    import argparse
    parser = argparse.ArgumentParser(description="Universal Bulk PDF Harvester (CLI Mode)")
    parser.add_argument("url", nargs="?", default="", help="Target URL to crawl (eGyanKosh, WBJEEB, WBCSC, etc.)")
    parser.add_argument("--max-pages", type=int, default=150, help="Maximum pages to crawl (default: 150)")
    parser.add_argument("--delay", type=float, default=0.5, help="Delay between requests in seconds")
    parser.add_argument("--output-dir", default="harvested_pdfs", help="Output directory for downloaded PDFs")
    args = parser.parse_args()

    url = args.url.strip()
    if not url:
        try:
            url = input("\n🔗 Enter Target URL to Harvest: ").strip()
        except (EOFError, KeyboardInterrupt):
            print("\nAborted.")
            sys.exit(0)

    if not url:
        print("❌ Error: No URL provided.")
        sys.exit(1)

    url = url.strip("'\"")
    if not urlparse(url).scheme:
        url = "https://" + url

    out_dir = Path(args.output_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    print("\n" + "=" * 60)
    print("🚀 Universal Bulk Document & PDF Harvester (CLI Mode)")
    print(f"🔗 Target: {url}")
    print(f"📁 Output: {out_dir.resolve()}")
    print("=" * 60 + "\n")

    downloader = WebDownloader(
        start_url=url,
        delay=args.delay,
        max_pages=args.max_pages,
        max_depth=5,
    )
    downloader.temp_dir = out_dir

    downloader.crawl()

    downloaded = [r for r in downloader.records if r.status == "Downloaded"]
    print("\n" + "=" * 60)
    print(f"✅ Crawl Complete! Downloaded {len(downloaded)} PDF document(s).")
    print(f"📁 Saved to: {out_dir.resolve()}")
    print("=" * 60 + "\n")

    csv_path = out_dir / "metadata.csv"
    with csv_path.open("w", newline="", encoding="utf-8-sig") as f:
        writer = csv.DictWriter(f, fieldnames=[
            "title", "authors", "date", "publisher", "subject",
            "description", "language", "item_type", "page_url",
            "pdf_url", "filename", "size_bytes", "status", "error"
        ])
        writer.writeheader()
        for rec in downloader.records:
            writer.writerow(rec.__dict__)
    print(f"📄 Metadata written to: {csv_path.name}")


# -------------------------------------------------------------
# Main Application Entry Point
# -------------------------------------------------------------

if __name__ == "__main__":
    if RUNNING_IN_STREAMLIT:
        render_streamlit_ui()
    else:
        run_cli()
