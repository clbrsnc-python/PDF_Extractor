#!/usr/bin/env python3
"""
Universal Bulk PDF Downloader - Streamlit Web App
-------------------------------------------------
Vibrant, colorful web interface styled after OmniWare educational portal.
Supports DSpace repositories, government portals (NTA / S3WaaS), and general websites.
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

# Suppress insecure SSL warnings
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
                # PDF dates usually look like D:YYYYMMDDHHmmSS
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
# Streamlit UI with OmniWare Styling
# -------------------------------------------------------------
st.set_page_config(
    page_title="OmniWare • Universal Bulk PDF Extractor",
    page_icon="🎓",
    layout="wide",
)

# Custom CSS matching the colorful OmniWare theme
st.markdown(
    """
    <style>
    @import url('https://fonts.googleapis.com/css2?family=Cinzel:wght@600;700;800&family=Plus+Jakarta+Sans:wght@400;500;600;700;800&display=swap');

    /* Global background */
    .stApp {
        background: #f4f7fb;
        font-family: 'Plus Jakarta Sans', sans-serif;
    }

    /* Top Navy & Gold Banner */
    .omni-top-banner {
        background: linear-gradient(135deg, #02163b 0%, #062b66 50%, #031c49 100%);
        border-bottom: 3px solid #d4af37;
        padding: 16px 28px;
        border-radius: 14px;
        display: flex;
        align-items: center;
        justify-content: space-between;
        margin-bottom: 20px;
        box-shadow: 0 8px 24px rgba(3, 27, 73, 0.15);
    }
    .omni-brand-left {
        display: flex;
        align-items: center;
        gap: 16px;
    }
    .omni-logo-badge {
        background: radial-gradient(circle, #ffe082 0%, #d4af37 100%);
        width: 52px;
        height: 52px;
        border-radius: 50%;
        display: flex;
        align-items: center;
        justify-content: center;
        font-size: 28px;
        box-shadow: 0 4px 12px rgba(212, 175, 55, 0.4);
    }
    .omni-brand-title {
        font-family: 'Cinzel', serif;
        font-size: 32px;
        font-weight: 800;
        letter-spacing: 0.5px;
        color: #f7d784;
        margin: 0;
        line-height: 1.1;
    }
    .omni-brand-sub {
        font-size: 13px;
        font-weight: 500;
        color: #f4f7fb;
        margin: 0;
        letter-spacing: 0.8px;
    }
    .omni-tagline {
        font-family: 'Cinzel', serif;
        font-style: italic;
        color: #ffd54f;
        font-size: 17px;
        letter-spacing: 1px;
    }
    .omni-designer {
        font-size: 12px;
        color: #b0c4de;
    }
    .omni-user-badge {
        background: rgba(255, 255, 255, 0.1);
        border: 1px solid rgba(255, 255, 255, 0.2);
        padding: 8px 16px;
        border-radius: 30px;
        display: flex;
        align-items: center;
        gap: 10px;
        color: #ffffff;
        font-size: 14px;
        font-weight: 600;
    }

    /* Sub Profile Banner */
    .profile-banner {
        background: #dbeffe;
        border: 1px solid #bfdbfe;
        border-radius: 14px;
        padding: 14px 22px;
        display: flex;
        align-items: center;
        justify-content: space-between;
        margin-bottom: 22px;
        box-shadow: 0 2px 8px rgba(30, 64, 175, 0.05);
    }
    .profile-info {
        display: flex;
        align-items: center;
        gap: 14px;
    }
    .profile-icon {
        background: #1e40af;
        color: white;
        width: 44px;
        height: 44px;
        border-radius: 50%;
        display: flex;
        align-items: center;
        justify-content: center;
        font-size: 22px;
    }
    .profile-title {
        font-size: 18px;
        font-weight: 700;
        color: #0f172a;
        margin: 0;
    }
    .profile-sub {
        font-size: 13px;
        color: #334155;
        margin: 0;
    }

    /* Section Header */
    .section-header-bar {
        background: linear-gradient(90deg, #0d3b84 0%, #1e58b8 100%);
        color: white;
        padding: 10px 18px;
        border-radius: 10px 10px 0 0;
        font-weight: 700;
        font-size: 16px;
        display: flex;
        align-items: center;
        gap: 8px;
    }
    .section-container {
        background: white;
        border: 1px solid #e2e8f0;
        border-radius: 0 0 14px 14px;
        padding: 20px;
        margin-bottom: 22px;
        box-shadow: 0 4px 12px rgba(0, 0, 0, 0.04);
    }

    /* Colorful Feature Cards */
    .feature-card {
        border-radius: 16px;
        padding: 20px 16px;
        text-align: center;
        height: 100%;
        display: flex;
        flex-direction: column;
        justify-content: space-between;
        align-items: center;
        transition: transform 0.2s ease, box-shadow 0.2s ease;
        box-shadow: 0 4px 12px rgba(0, 0, 0, 0.05);
    }
    .feature-card:hover {
        transform: translateY(-4px);
        box-shadow: 0 8px 20px rgba(0, 0, 0, 0.1);
    }
    .card-icon {
        width: 52px;
        height: 52px;
        border-radius: 12px;
        display: flex;
        align-items: center;
        justify-content: center;
        font-size: 26px;
        margin-bottom: 12px;
        box-shadow: 0 4px 10px rgba(0, 0, 0, 0.08);
    }
    .card-title {
        font-size: 16px;
        font-weight: 800;
        margin-bottom: 4px;
    }
    .card-sub {
        font-size: 12px;
        font-weight: 500;
        margin-bottom: 14px;
    }
    .card-btn {
        width: 32px;
        height: 32px;
        border-radius: 50%;
        background: white;
        display: flex;
        align-items: center;
        justify-content: center;
        font-size: 16px;
        font-weight: bold;
        box-shadow: 0 2px 6px rgba(0, 0, 0, 0.12);
    }

    /* Color variations matching the image */
    .card-blue {
        background: linear-gradient(180deg, #dbeafe 0%, #bfdbfe 100%);
        border: 1px solid #93c5fd;
        color: #1e3a8a;
    }
    .card-blue .card-icon { background: #2563eb; color: white; }
    .card-blue .card-title { color: #1e3a8a; }
    .card-blue .card-sub { color: #1d4ed8; }
    .card-blue .card-btn { color: #2563eb; }

    .card-green {
        background: linear-gradient(180deg, #dcfce7 0%, #bbf7d0 100%);
        border: 1px solid #86efac;
        color: #14532d;
    }
    .card-green .card-icon { background: #16a34a; color: white; }
    .card-green .card-title { color: #14532d; }
    .card-green .card-sub { color: #15803d; }
    .card-green .card-btn { color: #16a34a; }

    .card-orange {
        background: linear-gradient(180deg, #ffedd5 0%, #fed7aa 100%);
        border: 1px solid #fdba74;
        color: #7c2d12;
    }
    .card-orange .card-icon { background: #ea580c; color: white; }
    .card-orange .card-title { color: #7c2d12; }
    .card-orange .card-sub { color: #c2410c; }
    .card-orange .card-btn { color: #ea580c; }

    .card-purple {
        background: linear-gradient(180deg, #f3e8ff 0%, #e9d5ff 100%);
        border: 1px solid #d8b4fe;
        color: #581c87;
    }
    .card-purple .card-icon { background: #9333ea; color: white; }
    .card-purple .card-title { color: #581c87; }
    .card-purple .card-sub { color: #7e22ce; }
    .card-purple .card-btn { color: #9333ea; }

    .card-teal {
        background: linear-gradient(180deg, #ccfbf1 0%, #99f6e4 100%);
        border: 1px solid #5eead4;
        color: #134e4a;
    }
    .card-teal .card-icon { background: #0d9488; color: white; }
    .card-teal .card-title { color: #134e4a; }
    .card-teal .card-sub { color: #0f766e; }
    .card-teal .card-btn { color: #0d9488; }

    /* Recommendation warm banner */
    .rec-banner {
        background: #fffbeb;
        border: 1px solid #fde68a;
        border-radius: 12px;
        padding: 14px 20px;
        display: flex;
        align-items: center;
        justify-content: space-between;
        margin-top: 18px;
        margin-bottom: 24px;
    }
    .rec-left {
        display: flex;
        align-items: center;
        gap: 12px;
    }
    .rec-star {
        font-size: 26px;
        color: #f59e0b;
    }
    .rec-title {
        font-size: 15px;
        font-weight: 700;
        color: #78350f;
        margin: 0;
    }
    .rec-sub {
        font-size: 13px;
        color: #92400e;
        margin: 0;
    }

    /* Footer Banner */
    .omni-footer {
        background: #02163b;
        color: #ffd54f;
        text-align: center;
        padding: 12px;
        border-radius: 8px;
        font-family: 'Cinzel', serif;
        font-style: italic;
        font-size: 15px;
        letter-spacing: 1px;
        margin-top: 24px;
    }
    </style>
    """,
    unsafe_allow_html=True,
)

# 1. Top Navigation & Brand Banner (Matching the OmniWare theme)
st.markdown(
    """
    <div class="omni-top-banner">
        <div class="omni-brand-left">
            <div class="omni-logo-badge">🎓</div>
            <div>
                <h1 class="omni-brand-title">OmniWare</h1>
                <p class="omni-brand-sub">Smart Learning 24x7</p>
            </div>
        </div>
        <div style="text-align: center;">
            <div class="omni-tagline">Learn • Practice • Excel</div>
            <div class="omni-designer">Universal PDF Extractor Cloud</div>
        </div>
        <div class="omni-user-badge">
            <span>🔔 2</span>
            <span>👤 Welcome, User ▾</span>
        </div>
    </div>
    """,
    unsafe_allow_html=True,
)

# 2. Academic Profile / Breadcrumb Card
st.markdown(
    """
    <div class="profile-banner">
        <div class="profile-info">
            <div class="profile-icon">🎓</div>
            <div>
                <h2 class="profile-title">Bulk PDF Extractor System</h2>
                <p class="profile-sub">Universal Document Harvesting • Live Streaming • Rich Metadata Parser</p>
            </div>
        </div>
        <div style="background: white; padding: 6px 14px; border-radius: 20px; font-size: 13px; font-weight: 700; color: #1e40af; border: 1px solid #bfdbfe;">
            📊 Ready to Harvest &gt;
        </div>
    </div>
    """,
    unsafe_allow_html=True,
)

# 3. Colorful Quick Action Cards (5 vibrant cards matching the image)
col1, col2, col3, col4, col5 = st.columns(5)

with col1:
    st.markdown(
        """
        <div class="feature-card card-blue">
            <div class="card-icon">💬</div>
            <div>
                <div class="card-title">Paste URL</div>
                <div class="card-sub">Link • Detect • Target</div>
            </div>
            <div class="card-btn">→</div>
        </div>
        """,
        unsafe_allow_html=True,
    )

with col2:
    st.markdown(
        """
        <div class="feature-card card-green">
            <div class="card-icon">📖</div>
            <div>
                <div class="card-title">Deep Crawl</div>
                <div class="card-sub">Recursive • Sublinks</div>
            </div>
            <div class="card-btn">→</div>
        </div>
        """,
        unsafe_allow_html=True,
    )

with col3:
    st.markdown(
        """
        <div class="feature-card card-orange">
            <div class="card-icon">📋</div>
            <div>
                <div class="card-title">Auto Stream</div>
                <div class="card-sub">Extract • Stream • Verify</div>
            </div>
            <div class="card-btn">→</div>
        </div>
        """,
        unsafe_allow_html=True,
    )

with col4:
    st.markdown(
        """
        <div class="feature-card card-purple">
            <div class="card-icon">📚</div>
            <div>
                <div class="card-title">Full Metadata</div>
                <div class="card-sub">Author • Date • Manifest</div>
            </div>
            <div class="card-btn">→</div>
        </div>
        """,
        unsafe_allow_html=True,
    )

with col5:
    st.markdown(
        """
        <div class="feature-card card-teal">
            <div class="card-icon">📈</div>
            <div>
                <div class="card-title">ZIP Export</div>
                <div class="card-sub">1-Click • Bundle • Save</div>
            </div>
            <div class="card-btn">→</div>
        </div>
        """,
        unsafe_allow_html=True,
    )

st.write("")

# 4. Main Crawler Interface
with st.sidebar:
    st.header("⚙️ Crawler Settings")
    # Requirement 2: Default to "Deep Crawl (Follow sublinks)"
    crawl_mode = st.radio(
        "Crawl Mode",
        options=["Deep Crawl (Follow sublinks)", "Current Page Only"],
        index=0,  # Deep Crawl is default!
        help="'Deep Crawl' explores course blocks and connected subpages. 'Current Page Only' targets just the provided URL.",
    )
    max_depth = 2 if crawl_mode == "Deep Crawl (Follow sublinks)" else 0
    max_pages = st.number_input("Maximum Pages to Crawl", min_value=1, max_value=300, value=30)
    request_delay = st.slider("Request Delay (seconds)", min_value=0.1, max_value=2.0, value=0.5, step=0.1)

st.markdown('<div class="section-header-bar">🚀 Continue Extraction</div>', unsafe_allow_html=True)
with st.container():
    st.markdown('<div class="section-container">', unsafe_allow_html=True)
    target_url = st.text_input(
        "🔗 Paste Repository, Archive, or Webpage URL:",
        placeholder="https://egyankosh.ac.in/handle/123456789/... or https://jeemain.nta.nic.in/document-category/archive/page/11/",
    )
    start_btn = st.button("🚀 Start PDF Extraction", type="primary", use_container_width=True)
    st.markdown("</div>", unsafe_allow_html=True)

if start_btn:
    if not target_url.strip():
        st.warning("Please provide a valid URL to begin.")
    else:
        url = target_url.strip().strip("'\"")
        if not urlparse(url).scheme:
            url = "https://" + url

        with tempfile.TemporaryDirectory(prefix="pdf_extract_") as temp_dir:
            status_box = st.status("🔍 Initializing OmniWare crawler engine...", expanded=True)
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

            # Colorful metrics row
            mcol1, mcol2, mcol3 = st.columns(3)
            with mcol1:
                st.markdown(
                    f"""
                    <div style="background: #dbeafe; border-radius: 12px; padding: 16px; border-left: 6px solid #2563eb; box-shadow: 0 2px 8px rgba(0,0,0,0.04);">
                        <div style="font-size: 13px; font-weight: 700; color: #1e40af;">PAGES VISITED</div>
                        <div style="font-size: 32px; font-weight: 800; color: #1e3a8a;">{len(downloader.visited)}</div>
                    </div>
                    """,
                    unsafe_allow_html=True,
                )
            with mcol2:
                st.markdown(
                    f"""
                    <div style="background: #dcfce7; border-radius: 12px; padding: 16px; border-left: 6px solid #16a34a; box-shadow: 0 2px 8px rgba(0,0,0,0.04);">
                        <div style="font-size: 13px; font-weight: 700; color: #15803d;">PDFs HARVESTED</div>
                        <div style="font-size: 32px; font-weight: 800; color: #14532d;">{downloaded_count}</div>
                    </div>
                    """,
                    unsafe_allow_html=True,
                )
            with mcol3:
                st.markdown(
                    f"""
                    <div style="background: #fee2e2; border-radius: 12px; padding: 16px; border-left: 6px solid #dc2626; box-shadow: 0 2px 8px rgba(0,0,0,0.04);">
                        <div style="font-size: 13px; font-weight: 700; color: #b91c1c;">DOWNLOAD ERRORS</div>
                        <div style="font-size: 32px; font-weight: 800; color: #991b1b;">{failed_count}</div>
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
                st.info("No PDF documents were located at the provided target.")

# 5. Recommendation / Tip Banner (matching the warm yellow banner)
st.markdown(
    """
    <div class="rec-banner">
        <div class="rec-left">
            <span class="rec-star">★</span>
            <div>
                <p class="rec-title">Pro Tip for Educational Archives</p>
                <p class="rec-sub">For eGyanKosh course blocks, use 'Deep Crawl'. For single notice/circular tables (like NTA Page 11), switch to 'Current Page Only'.</p>
            </div>
        </div>
        <div style="background: white; border: 1px solid #fcd34d; padding: 6px 14px; border-radius: 20px; font-size: 13px; font-weight: 700; color: #b45309;">
            💡 Smart Tip
        </div>
    </div>
    """,
    unsafe_allow_html=True,
)

# 6. Navy & Gold Bottom Banner
st.markdown(
    """
    <div class="omni-footer">
        Knowledge Today... Success Tomorrow...
    </div>
    """,
    unsafe_allow_html=True,
)
