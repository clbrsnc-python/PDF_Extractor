#!/usr/bin/env python3
"""
Universal Bulk PDF Extractor - Streamlit Web App
-------------------------------------------------
Streamlined, highlighted interface with compact colorful badges.
"""

from __future__ import annotations

import csv
import io
import re
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
import streamlit as st

# Optional pypdf for reading internal PDF metadata
try:
    import pypdf
    HAS_PYPDF = True
except Exception:
    HAS_PYPDF = False

# Suppress insecure SSL warnings for government/educational portals
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/128.0.0.0 Safari/537.36"
)
HANDLE_RE = re.compile(r"/handle/(\d+)/([^/?#]+)", re.I)
BAD_CHARS = re.compile(r'[<>:"/\\|?*\x00-\x1f]')
SKIPPABLE_EXTENSIONS = {
    ".pdf", ".png", ".jpg", ".jpeg", ".gif", ".webp", ".svg", ".ico",
    ".css", ".js", ".mp4", ".mp3", ".zip", ".tar", ".gz", ".7z",
    ".exe", ".dmg", ".apk"
}


def clean_text(value: str) -> str:
    return re.sub(r"\s+", " ", unescape(value or "")).strip()


def safe_filename(name: str, fallback: str = "download.pdf") -> str:
    name = unquote(name or "").strip()
    name = BAD_CHARS.sub("_", name)
    name = name.strip(" .")
    if not name:
        name = fallback
    if not name.lower().endswith(".pdf"):
        name += ".pdf"
    return name[:180]


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

            except Exception as exc:
                self.log(f"⚠️ Could not load `{url}`: {exc}")

    def process_dspace(self, soup: BeautifulSoup, page_url: str, queue: deque, depth: int):
        is_item = bool(soup.select_one("table.itemDisplayTable") or
                       soup.find("meta", attrs={"name": re.compile(r"citation_pdf_url", re.I)}) or
                       "files in this item" in soup.get_text(" ", strip=True).lower())

        if is_item:
            meta = self.extract_dspace_metadata(soup)
            pdf_links = self.extract_dspace_pdf_links(soup, page_url)
            for pdf_url, label in pdf_links:
                raw_name = label or PurePosixPath(urlparse(pdf_url).path).name
                filename = safe_filename(raw_name)
                self.download_pdf(pdf_url, filename, page_url, meta=meta)
            return

        main = soup.find("main") or soup.find(id="content") or soup.body or soup
        for a in main.find_all("a", href=True):
            if a.find_parent(class_="breadcrumb") or a.find_parent("header") or a.find_parent("footer"):
                continue
            child_url = canonical(urljoin(page_url, a["href"]))
            if same_site(child_url, self.host) and HANDLE_RE.search(urlparse(child_url).path):
                if child_url not in self.visited:
                    queue.append((child_url, depth + 1))

    def extract_generic_page_metadata(self, soup: BeautifulSoup, page_url: str) -> dict:
        """Extracts Dublin Core, OpenGraph, and standard meta tags from standalone pages."""
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

        # 1. Parse tables: extract title, date, and PDF link from rows
        for table in soup.find_all("table"):
            headers = [clean_text(th.get_text(" ", strip=True)).lower() for th in table.find_all("th")]
            date_col_idx = -1
            for idx, h in enumerate(headers):
                if any(w in h for w in ("date", "year", "published", "issue")):
                    date_col_idx = idx
                    break

            for row in table.find_all("tr"):
                cells = row.find_all("td")
                if len(cells) >= 2:
                    for a in row.find_all("a", href=True):
                        href = urljoin(page_url, a["href"])
                        u = urlparse(href)
                        if u.path.lower().endswith(".pdf") or ".pdf?" in href.lower():
                            first_cell_text = clean_text(cells[0].get_text(" ", strip=True))
                            title = first_cell_text if len(first_cell_text) > 3 else PurePosixPath(u.path).name
                            filename = safe_filename(title)

                            row_meta = dict(page_meta)
                            row_meta["title"] = title
                            if date_col_idx != -1 and date_col_idx < len(cells):
                                d_text = clean_text(cells[date_col_idx].get_text(" ", strip=True))
                                if d_text:
                                    row_meta["date"] = d_text

                            self.download_pdf(href, filename, page_url, meta=row_meta, page_title=title)

        # 2. Parse any direct PDF links outside tables
        for a in soup.find_all("a", href=True):
            href = urljoin(page_url, a["href"])
            u = urlparse(href)
            if u.path.lower().endswith(".pdf") or ".pdf?" in href.lower():
                link_text = clean_text(a.get_text(" ", strip=True))
                raw_name = link_text if link_text and not any(w in link_text.lower() for w in ["pdf", "download", "view", "link"]) else PurePosixPath(u.path).name
                filename = safe_filename(raw_name or PurePosixPath(u.path).name)

                link_meta = dict(page_meta)
                link_meta["title"] = raw_name or link_meta.get("title", filename)
                self.download_pdf(href, filename, page_url, meta=link_meta, page_title=link_meta["title"])

        # 3. Follow subpages within depth limit
        if depth < self.max_depth:
            for a in soup.find_all("a", href=True):
                href = canonical(urljoin(page_url, a["href"]))
                u = urlparse(href)
                if u.scheme not in ("http", "https") or not same_site(href, self.host):
                    continue
                if u.path.lower().endswith(".pdf") or ".pdf?" in href.lower():
                    continue
                if any(u.path.lower().endswith(ext) for ext in SKIPPABLE_EXTENSIONS):
                    continue
                if href not in self.visited and not any(href == q_url for q_url, _ in queue):
                    queue.append((href, depth + 1))

    def extract_dspace_pdf_links(self, soup: BeautifulSoup, page_url: str):
        found = []
        seen_paths = set()
        generic_labels = {"view", "open", "view/open", "download", "show", "thumbnail", ""}

        for table in soup.find_all("table"):
            for row in table.find_all("tr"):
                cells = row.find_all("td")
                row_links = [urljoin(page_url, a["href"]) for a in row.find_all("a", href=True) if "/bitstream/" in a["href"].lower()]
                if not row_links:
                    continue

                filename = ""
                for a in row.find_all("a", href=True):
                    txt = clean_text(a.get_text(" ", strip=True))
                    if txt and txt.lower() not in generic_labels:
                        filename = txt
                        break
                if not filename and cells:
                    first_cell = clean_text(cells[0].get_text(" ", strip=True))
                    if first_cell and first_cell.lower() not in generic_labels:
                        filename = first_cell

                best_link = row_links[0]
                for l in row_links:
                    if "isallowed=y" in l.lower():
                        best_link = l
                        break

                u = urlparse(best_link)
                if u.path.lower() in seen_paths:
                    continue
                seen_paths.add(u.path.lower())

                if not filename:
                    filename = PurePosixPath(u.path).name
                if "isallowed=" not in best_link.lower():
                    best_link += ("&" if "?" in best_link else "?") + "isAllowed=y"

                found.append((best_link, filename))

        for a in soup.find_all("a", href=True):
            href = urljoin(page_url, a["href"])
            u = urlparse(href)
            if "/bitstream/" in u.path.lower() and u.path.lower() not in seen_paths:
                label = clean_text(a.get_text(" ", strip=True))
                name = PurePosixPath(u.path).name
                final_name = name if label.lower() in generic_labels else (label or name)
                if "isallowed=" not in href.lower():
                    href += ("&" if "?" in href else "?") + "isAllowed=y"
                seen_paths.add(u.path.lower())
                found.append((href, final_name))

        return found

    def extract_dspace_metadata(self, soup: BeautifulSoup):
        data = {}
        for tag in soup.find_all("meta"):
            key = (tag.get("name") or "").strip()
            value = clean_text(tag.get("content", ""))
            if key and value and (key.lower().startswith("dc.") or key.lower().startswith("citation_")):
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

    def download_pdf(self, pdf_url: str, base_filename: str, page_url: str,
                     meta: dict | None = None, page_title: str = ""):
        if pdf_url in self.pdf_url_seen:
            return
        self.pdf_url_seen.add(pdf_url)

        meta = dict(meta or {})
        item_title = meta.get("title") or page_title or base_filename

        target_path = self.temp_dir / base_filename
        counter = 2
        stem = base_filename[:-4]
        while target_path.exists() and target_path not in [p for _, p, _ in self.downloaded_files]:
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

            if b"%PDF-" not in signature:
                target_path.unlink(missing_ok=True)
                raise ValueError(f"Content is not a PDF (content-type: '{content_type or 'unknown'}')")

            # Extract internal PDF metadata to fill in missing fields (author, date, subject)
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
                item_type=meta.get("type", "PDF Document"),
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
                item_type=meta.get("type", "PDF Document"),
                page_url=page_url,
                pdf_url=pdf_url,
                filename=filename,
                size_bytes=0,
                status="Failed",
                error=str(exc),
            ))
            self.log(f"❌ Failed `{filename}`: {exc}")


def build_zip_in_memory(downloaded_files, records) -> bytes:
    zip_buffer = io.BytesIO()
    with zipfile.ZipFile(zip_buffer, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for filename, local_path, _ in downloaded_files:
            if local_path.exists():
                zf.write(local_path, f"PDFs/{filename}")

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
        zf.writestr("metadata.csv", "\ufeff" + csv_buf.getvalue())

    return zip_buffer.getvalue()


# -------------------------------------------------------------
# Streamlit UI Configuration
# -------------------------------------------------------------
st.set_page_config(
    page_title="Bulk PDF Extractor System",
    page_icon="🎓",
    layout="wide",
)

# Custom Styling
st.markdown(
    """
    <style>
    @import url('https://fonts.googleapis.com/css2?family=Plus+Jakarta+Sans:wght@400;500;600;700;800&display=swap');

    .stApp {
        background: #f4f7fb;
        font-family: 'Plus Jakarta Sans', sans-serif;
    }

    /* Main Academic Header */
    .system-header-card {
        background: linear-gradient(135deg, #021a44 0%, #082d6c 60%, #031e50 100%);
        border-bottom: 3px solid #d4af37;
        border-radius: 14px;
        padding: 20px 26px;
        display: flex;
        align-items: center;
        justify-content: space-between;
        margin-bottom: 22px;
        box-shadow: 0 6px 20px rgba(2, 26, 68, 0.12);
    }
    .system-header-left {
        display: flex;
        align-items: center;
        gap: 16px;
    }
    .system-header-icon {
        background: #1e40af;
        border: 2px solid #60a5fa;
        color: white;
        width: 48px;
        height: 48px;
        border-radius: 12px;
        display: flex;
        align-items: center;
        justify-content: center;
        font-size: 26px;
        box-shadow: 0 4px 12px rgba(0,0,0,0.15);
    }
    .system-title {
        font-size: 24px;
        font-weight: 800;
        color: #ffffff;
        margin: 0;
        letter-spacing: 0.3px;
    }
    .system-subtitle {
        font-size: 13px;
        font-weight: 500;
        color: #bfdbfe;
        margin: 0;
        letter-spacing: 0.4px;
    }
    .system-badge-right {
        background: rgba(255, 255, 255, 0.12);
        border: 1px solid rgba(255, 255, 255, 0.25);
        color: #fef08a;
        font-weight: 700;
        font-size: 13px;
        padding: 6px 14px;
        border-radius: 20px;
    }

    /* PROMINENTLY HIGHLIGHTED URL INPUT CONTAINER */
    .highlighted-input-box {
        background: #ffffff;
        border: 2px solid #2563eb;
        border-radius: 16px;
        padding: 24px 26px;
        margin-bottom: 20px;
        box-shadow: 0 10px 28px rgba(37, 99, 235, 0.12);
        position: relative;
    }
    .input-label-highlight {
        font-size: 18px;
        font-weight: 800;
        color: #0f172a;
        display: flex;
        align-items: center;
        gap: 8px;
        margin-bottom: 8px;
    }
    .input-sub-tip {
        font-size: 13px;
        color: #64748b;
        margin-bottom: 14px;
    }

    /* COMPACT COLORFUL FEATURE TILES (Reduced Size, No Arrows) */
    .compact-tile {
        border-radius: 10px;
        padding: 10px 12px;
        text-align: center;
        height: 100%;
        display: flex;
        align-items: center;
        justify-content: center;
        gap: 10px;
        box-shadow: 0 2px 6px rgba(0, 0, 0, 0.04);
        margin-bottom: 20px;
    }
    .tile-icon {
        font-size: 18px;
        line-height: 1;
    }
    .tile-text-wrap {
        text-align: left;
    }
    .tile-title {
        font-size: 12px;
        font-weight: 800;
        line-height: 1.2;
    }
    .tile-desc {
        font-size: 10px;
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

    /* Footer Banner */
    .omni-footer {
        background: #02163b;
        color: #ffd54f;
        text-align: center;
        padding: 10px;
        border-radius: 8px;
        font-style: italic;
        font-size: 14px;
        letter-spacing: 0.8px;
        margin-top: 26px;
    }
    </style>
    """,
    unsafe_allow_html=True,
)

# 1. Main System Header (Starts directly with Bulk PDF Extractor System)
st.markdown(
    """
    <div class="system-header-card">
        <div class="system-header-left">
            <div class="system-header-icon">🎓</div>
            <div>
                <h1 class="system-title">Bulk PDF Extractor System</h1>
                <p class="system-subtitle">Universal Document Harvesting • Live Streaming • Rich Metadata Parser</p>
            </div>
        </div>
        <div class="system-badge-right">
            ⚡ Ready to Extract
        </div>
    </div>
    """,
    unsafe_allow_html=True,
)

# Sidebar Settings (Default to Deep Crawl)
with st.sidebar:
    st.header("⚙️ Crawler Settings")
    crawl_mode = st.radio(
        "Crawl Mode",
        options=["Deep Crawl (Follow sublinks)", "Current Page Only"],
        index=0,  # Deep Crawl is default
        help="'Deep Crawl' explores course blocks and connected subpages. 'Current Page Only' targets just the provided URL.",
    )
    max_depth = 2 if crawl_mode == "Deep Crawl (Follow sublinks)" else 0
    max_pages = st.number_input("Maximum Pages to Crawl", min_value=1, max_value=300, value=30)
    request_delay = st.slider("Request Delay (seconds)", min_value=0.1, max_value=2.0, value=0.5, step=0.1)

# 2. PROMINENTLY HIGHLIGHTED URL INPUT SECTION (First and Center)
st.markdown(
    """
    <div class="highlighted-input-box">
        <div class="input-label-highlight">
            <span>🔗 Paste Repository, Archive, or Webpage URL:</span>
        </div>
        <div class="input-sub-tip">
            Supports eGyanKosh course units, government archive tables (NTA/JEE), and general PDF resource links.
        </div>
    </div>
    """,
    unsafe_allow_html=True,
)

url_col, btn_col = st.columns([4, 1])
with url_col:
    target_url = st.text_input(
        "Enter Target URL",
        placeholder="https://egyankosh.ac.in/handle/123456789/... or https://jeemain.nta.nic.in/document-category/archive/page/11/",
        label_visibility="collapsed",
    )
with btn_col:
    start_btn = st.button("🚀 Start Extraction", type="primary", use_container_width=True)

# 3. COMPACT COLORFUL STATUS TILES (Reduced Size, No Arrows)
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

# 4. Crawler Execution & Results
if start_btn:
    if not target_url.strip():
        st.warning("Please enter a valid URL to extract PDFs.")
    else:
        url = target_url.strip().strip("'\"")
        if not urlparse(url).scheme:
            url = "https://" + url

        with tempfile.TemporaryDirectory(prefix="pdf_extract_") as temp_dir:
            status_box = st.status("🔍 Initializing extraction engine...", expanded=True)
            downloader = WebDownloader(
                start_url=url,
                delay=request_delay,
                max_pages=max_pages,
                max_depth=max_depth,
                status_container=status_box,
            )
            downloader.temp_dir = Path(temp_dir)

            progress_bar = st.progress(0.0)
            downloader.crawl(progress_bar=progress_bar)
            progress_bar.progress(1.0)
            status_box.update(label="✅ Extraction & Metadata Parsing Complete!", state="complete", expanded=False)

            downloaded_count = sum(1 for r in downloader.records if r.status == "Downloaded")
            failed_count = sum(1 for r in downloader.records if r.status == "Failed")

            # Metric KPI Cards
            mcol1, mcol2, mcol3 = st.columns(3)
            with mcol1:
                st.markdown(
                    f"""
                    <div style="background: #e0f2fe; border-radius: 12px; padding: 14px; border-left: 5px solid #0284c7;">
                        <div style="font-size: 12px; font-weight: 700; color: #0369a1;">PAGES EXPLORED</div>
                        <div style="font-size: 28px; font-weight: 800; color: #0c4a6e;">{len(downloader.visited)}</div>
                    </div>
                    """,
                    unsafe_allow_html=True,
                )
            with mcol2:
                st.markdown(
                    f"""
                    <div style="background: #dcfce7; border-radius: 12px; padding: 14px; border-left: 5px solid #16a34a;">
                        <div style="font-size: 12px; font-weight: 700; color: #15803d;">PDFs DOWNLOADED</div>
                        <div style="font-size: 28px; font-weight: 800; color: #14532d;">{downloaded_count}</div>
                    </div>
                    """,
                    unsafe_allow_html=True,
                )
            with mcol3:
                st.markdown(
                    f"""
                    <div style="background: #fee2e2; border-radius: 12px; padding: 14px; border-left: 5px solid #dc2626;">
                        <div style="font-size: 12px; font-weight: 700; color: #b91c1c;">DOWNLOAD ERRORS</div>
                        <div style="font-size: 28px; font-weight: 800; color: #991b1b;">{failed_count}</div>
                    </div>
                    """,
                    unsafe_allow_html=True,
                )

            st.write("")

            if downloaded_count > 0:
                zip_data = build_zip_in_memory(downloader.downloaded_files, downloader.records)

                st.download_button(
                    label="📥 Download All Harvested PDFs + Metadata (ZIP)",
                    data=zip_data,
                    file_name="harvested_pdfs.zip",
                    mime="application/zip",
                    type="primary",
                    use_container_width=True,
                )

                st.subheader("📋 Document Manifest & Metadata")
                manifest_view = [
                    {
                        "Document Title": r.title,
                        "Author / Contributor": r.authors or "—",
                        "Issue Date": r.date or "—",
                        "Publisher / Source": r.publisher or "—",
                        "File Name": r.filename,
                        "Size (KB)": round(r.size_bytes / 1024, 1),
                        "Status": r.status,
                    }
                    for r in downloader.records
                ]
                st.dataframe(manifest_view, use_container_width=True)
            else:
                st.info("No PDF documents were found at the provided URL.")

# 5. Footer Banner
st.markdown(
    """
    <div class="omni-footer">
        Knowledge Today... Success Tomorrow...
    </div>
    """,
    unsafe_allow_html=True,
)
