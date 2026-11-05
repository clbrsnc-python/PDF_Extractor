#!/usr/bin/env python3
"""
Universal Bulk PDF Downloader - Streamlit Web App
-------------------------------------------------
Web interface for extracting PDFs from eGyanKosh (DSpace), government portals
(like NTA / S3WaaS), and general websites.

Deployable to Streamlit Community Cloud (share.streamlit.io).
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

# Suppress insecure SSL warnings for government/educational sites
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

        engine_name = "DSpace Repository Engine (eGyanKosh)" if self.is_dspace_repo else "Document Portal Engine (NTA / Web)"
        self.log(f"🔎 **Engine Detected:** {engine_name}")

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

                if "application/pdf" in content_type or url.lower().endswith(".pdf"):
                    filename = safe_filename(PurePosixPath(urlparse(url).path).name)
                    self.download_pdf(url, filename, url, page_title="Direct PDF Link")
                    continue

                if "text/html" not in content_type and "application/xhtml" not in content_type:
                    continue

                soup = BeautifulSoup(response.text, "html.parser")
                if first_page:
                    self.detect_mode(soup, response.url)
                    first_page = False

                self.log(f"📄 Page {len(self.visited)}: `{url}`")

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

    def process_generic(self, soup: BeautifulSoup, page_url: str, queue: deque, depth: int):
        page_title = clean_text(soup.title.get_text(" ", strip=True)) if soup.title else ""

        # 1. Parse tables for titles (common on government and archive sites)
        for row in soup.find_all("tr"):
            cells = row.find_all(["td", "th"])
            if len(cells) >= 2:
                for a in row.find_all("a", href=True):
                    href = urljoin(page_url, a["href"])
                    u = urlparse(href)
                    if u.path.lower().endswith(".pdf") or ".pdf?" in href.lower():
                        first_cell_text = clean_text(cells[0].get_text(" ", strip=True))
                        title = first_cell_text if len(first_cell_text) > 3 else PurePosixPath(u.path).name
                        filename = safe_filename(title)
                        self.download_pdf(href, filename, page_url, page_title=title)

        # 2. Parse any direct PDF links on the page
        for a in soup.find_all("a", href=True):
            href = urljoin(page_url, a["href"])
            u = urlparse(href)
            if u.path.lower().endswith(".pdf") or ".pdf?" in href.lower():
                link_text = clean_text(a.get_text(" ", strip=True))
                raw_name = link_text if link_text and not any(w in link_text.lower() for w in ["pdf", "download", "view", "link"]) else PurePosixPath(u.path).name
                filename = safe_filename(raw_name or PurePosixPath(u.path).name)
                self.download_pdf(href, filename, page_url, page_title=page_title)

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

        meta = meta or {}
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

            self.downloaded_files.append((filename, target_path, pdf_url))
            self.records.append(DownloadRecord(
                title=item_title,
                authors=meta.get("authors", ""),
                date=meta.get("date", ""),
                publisher=meta.get("publisher", ""),
                subject=meta.get("subject", ""),
                description=meta.get("description", ""),
                language=meta.get("language", ""),
                item_type=meta.get("type", ""),
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
                item_type=meta.get("type", ""),
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
# Streamlit UI
# -------------------------------------------------------------
st.set_page_config(
    page_title="Universal Bulk PDF Extractor",
    page_icon="📚",
    layout="wide",
)

st.title("📚 Universal Bulk PDF Extractor")
st.markdown(
    "Extract and download PDFs in bulk from **eGyanKosh (IGNOU / DSpace)**, "
    "**government exam portals (NTA / JEE / S3WaaS)**, and general websites."
)

with st.sidebar:
    st.header("⚙️ Configuration")
    crawl_mode = st.radio(
        "Crawl Mode",
        options=["Current Page Only", "Deep Crawl (Follow sublinks)"],
        index=0,
        help="Use 'Current Page Only' for notice or archive pages (like NTA page 11). Use 'Deep Crawl' for complete eGyanKosh courses.",
    )
    max_depth = 0 if crawl_mode == "Current Page Only" else 2
    max_pages = st.number_input("Maximum Pages to Crawl", min_value=1, max_value=200, value=25)
    request_delay = st.slider("Request Delay (seconds)", min_value=0.1, max_value=2.0, value=0.5, step=0.1)

target_url = st.text_input(
    "🔗 Enter URL to extract PDFs from:",
    placeholder="e.g. https://jeemain.nta.nic.in/document-category/archive/page/11/ or https://egyankosh.ac.in/handle/123456789/72701",
)

if st.button("🚀 Start PDF Extraction", type="primary"):
    if not target_url.strip():
        st.warning("Please enter a valid URL.")
    else:
        url = target_url.strip().strip("'\"")
        if not urlparse(url).scheme:
            url = "https://" + url

        with tempfile.TemporaryDirectory(prefix="pdf_extract_") as temp_dir:
            status_box = st.status("🔍 Initializing crawler...", expanded=True)
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
            status_box.update(label="✅ Extraction Completed!", state="complete", expanded=False)

            downloaded_count = sum(1 for r in downloader.records if r.status == "Downloaded")
            failed_count = sum(1 for r in downloader.records if r.status == "Failed")

            col1, col2, col3 = st.columns(3)
            col1.metric("Pages Visited", len(downloader.visited))
            col2.metric("PDFs Downloaded", downloaded_count)
            col3.metric("Failed Downloads", failed_count)

            if downloaded_count > 0:
                zip_data = build_zip_in_memory(downloader.downloaded_files, downloader.records)
                st.download_button(
                    label="📥 Download All Extracted PDFs (ZIP)",
                    data=zip_data,
                    file_name="extracted_pdfs.zip",
                    mime="application/zip",
                    type="primary",
                )

                st.subheader("📋 Downloaded Files Manifest")
                summary_data = [
                    {
                        "Filename": r.filename,
                        "Title": r.title,
                        "Size (KB)": round(r.size_bytes / 1024, 1),
                        "Status": r.status,
                    }
                    for r in downloader.records
                ]
                st.dataframe(summary_data, use_container_width=True)
            else:
                st.info("No PDF files were found at the provided URL.")