#!/usr/bin/env python3
"""Pin the latest public version of Kirk's Yang--Mills preprint.

The script records immutable Zenodo metadata, byte hashes, and a compact
theorem-heading inventory.  It intentionally does not redistribute the PDF or
claim that any theorem in it is correct.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any


FROZEN_RECORD_ID = "19614728"
CONCEPT_DOI = "10.5281/zenodo.18837539"
API_ROOT = "https://zenodo.org/api/records"
USER_AGENT = "millennium-braid-source-audit/1.0"
TARGETS = (
    "Theorem 7.8",
    "Corollary 7.12",
    "Theorem 8.6",
    "Theorem 9.10",
    "Lemma 9.12",
    "Corollary 9.13",
)


def fetch(url: str, destination: Path | None = None) -> tuple[bytes, str]:
    """GET a public URL with bounded retry and return bytes plus final URL."""
    last_error: Exception | None = None
    for attempt in range(7):
        request = urllib.request.Request(
            url,
            headers={"User-Agent": USER_AGENT, "Accept": "*/*"},
        )
        try:
            with urllib.request.urlopen(request, timeout=60) as response:
                final_url = response.geturl()
                if destination is None:
                    return response.read(), final_url
                digest = bytearray()
                with destination.open("wb") as stream:
                    while chunk := response.read(1024 * 1024):
                        stream.write(chunk)
                        digest.extend(chunk)
                return bytes(digest), final_url
        except urllib.error.HTTPError as error:
            last_error = error
            if error.code != 429 and error.code < 500:
                raise
        except urllib.error.URLError as error:
            last_error = error
        time.sleep(min(2**attempt, 32))
    assert last_error is not None
    raise last_error


def fetch_json(url: str, path: Path) -> tuple[dict[str, Any], str]:
    raw, final_url = fetch(url)
    path.write_bytes(raw)
    value = json.loads(raw)
    if not isinstance(value, dict):
        raise TypeError(f"Expected JSON object from {url}")
    return value, final_url


def record_summary(record: dict[str, Any]) -> dict[str, Any]:
    metadata = record.get("metadata", {})
    return {
        "id": str(record.get("id", "")),
        "doi": record.get("doi") or metadata.get("doi"),
        "concept_doi": record.get("conceptdoi") or metadata.get("conceptdoi"),
        "version": metadata.get("version"),
        "title": metadata.get("title"),
        "publication_date": metadata.get("publication_date"),
        "created": record.get("created"),
        "updated": record.get("updated"),
        "links": {
            key: record.get("links", {}).get(key)
            for key in ("self", "html", "latest", "latest_html", "versions")
        },
    }


def version_records(base_record: dict[str, Any]) -> tuple[list[dict[str, Any]], str | None]:
    versions_url = base_record.get("links", {}).get("versions")
    if not versions_url:
        return [base_record], None
    page, final_url = fetch_json(versions_url, Path("kirk_versions.json"))
    hits = page.get("hits", {}).get("hits", [])
    records = [hit for hit in hits if isinstance(hit, dict)]
    return records or [base_record], final_url


def choose_latest(base_record: dict[str, Any], versions: list[dict[str, Any]]) -> tuple[dict[str, Any], str]:
    latest_url = base_record.get("links", {}).get("latest")
    if latest_url:
        latest, final_url = fetch_json(latest_url, Path("kirk_latest_record.json"))
        return latest, final_url
    # Defensive fallback if an older Zenodo schema omits links.latest.
    latest = max(
        versions,
        key=lambda item: (str(item.get("created", "")), str(item.get("id", ""))),
    )
    Path("kirk_latest_record.json").write_text(
        json.dumps(latest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return latest, latest.get("links", {}).get("self", "")


def pdf_entry(record: dict[str, Any]) -> dict[str, Any]:
    files = record.get("files", [])
    pdfs = [item for item in files if str(item.get("key", "")).lower().endswith(".pdf")]
    if len(pdfs) != 1:
        raise RuntimeError(f"Expected exactly one PDF; found {len(pdfs)}")
    return pdfs[0]


def file_url(entry: dict[str, Any]) -> str:
    links = entry.get("links", {})
    value = links.get("content") or links.get("self")
    if not value:
        raise RuntimeError("Zenodo file entry has no content URL")
    return value


def hash_file(path: Path) -> dict[str, Any]:
    raw = path.read_bytes()
    return {
        "size": len(raw),
        "md5": hashlib.md5(raw).hexdigest(),  # provenance, not security
        "sha256": hashlib.sha256(raw).hexdigest(),
    }


def extract_inventory(pdf: Path, label: str) -> dict[str, Any]:
    text_path = Path(f"{label}.txt")
    subprocess.run(["pdftotext", "-layout", str(pdf), str(text_path)], check=True)
    text = text_path.read_text(encoding="utf-8", errors="replace")
    pages = text.split("\f")
    heading_re = re.compile(
        r"^\s*(Theorem|Corollary|Lemma|Proposition)\s+([0-9]+\.[0-9]+)\b.*$",
        re.MULTILINE,
    )
    headings: list[dict[str, Any]] = []
    for page_number, page in enumerate(pages, start=1):
        for match in heading_re.finditer(page):
            line = match.group(0).strip()
            headings.append(
                {
                    "kind": match.group(1),
                    "number": match.group(2),
                    "page": page_number,
                    "line": " ".join(line.split())[:240],
                }
            )
    targets = {
        target: [
            {"page": number, "line": " ".join(line.strip().split())[:240]}
            for number, page in enumerate(pages, start=1)
            for line in page.splitlines()
            if target in line
        ]
        for target in TARGETS
    }
    return {
        "page_count": max(0, len(pages) - (1 if pages and not pages[-1].strip() else 0)),
        "headings": headings,
        "targets": targets,
    }


def main() -> None:
    frozen, frozen_final = fetch_json(
        f"{API_ROOT}/{FROZEN_RECORD_ID}", Path("kirk_frozen_record.json")
    )
    versions, versions_final = version_records(frozen)
    latest, latest_final = choose_latest(frozen, versions)

    version_summaries = [record_summary(item) for item in versions]
    frozen_summary = record_summary(frozen)
    latest_summary = record_summary(latest)
    if latest_summary["concept_doi"] not in (None, CONCEPT_DOI):
        raise RuntimeError(f"Unexpected concept DOI: {latest_summary['concept_doi']}")

    source_reports: dict[str, Any] = {}
    for label, record in (("frozen", frozen), ("latest", latest)):
        pdf = Path(f"kirk_{label}.pdf")
        entry = pdf_entry(record)
        _, final_file_url = fetch(file_url(entry), pdf)
        hashes = hash_file(pdf)
        declared = entry.get("checksum")
        if isinstance(declared, str) and declared.startswith("md5:"):
            if hashes["md5"] != declared.removeprefix("md5:"):
                raise RuntimeError(f"MD5 mismatch for {label}")
        source_reports[label] = {
            "record": record_summary(record),
            "file": {
                "key": entry.get("key"),
                "declared_checksum": declared,
                "declared_size": entry.get("size"),
                "final_url": final_file_url,
                **hashes,
            },
            "inventory": extract_inventory(pdf, label),
        }

    frozen_targets = source_reports["frozen"]["inventory"]["targets"]
    latest_targets = source_reports["latest"]["inventory"]["targets"]
    report = {
        "status": "source provenance only; no mathematical validity claim",
        "concept_doi": CONCEPT_DOI,
        "frozen_request_final_url": frozen_final,
        "versions_request_final_url": versions_final,
        "latest_request_final_url": latest_final,
        "versions": version_summaries,
        "frozen": source_reports["frozen"],
        "latest": source_reports["latest"],
        "load_bearing_target_delta": {
            target: {
                "frozen": frozen_targets[target],
                "latest": latest_targets[target],
                "changed": frozen_targets[target] != latest_targets[target],
            }
            for target in TARGETS
        },
    }
    Path("kirk_source_probe_report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
