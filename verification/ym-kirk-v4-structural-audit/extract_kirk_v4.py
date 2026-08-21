#!/usr/bin/env python3
"""Bounded structural extraction for the public Kirk v4 Yang--Mills PDF.

The report is intentionally a sparse theorem/dependency audit.  It does not
reproduce the manuscript and it does not decide whether the claimed theorem is
correct.
"""
from __future__ import annotations

import argparse
import hashlib
import re
import subprocess
from pathlib import Path

DECL_RE = re.compile(
    r"^\s*(?:Main Theorem|Theorem|Proposition|Lemma|Corollary|Definition|"
    r"Assumption|Hypothesis|Standard Input|External Input|Input Register)\b",
    re.IGNORECASE,
)
SECTION_RE = re.compile(
    r"^\s*(?:(?:[0-9]+(?:\.[0-9]+)*)|(?:Appendix\s+[A-Z]))[.)]?\s+\S.{2,130}$"
)

PHRASES = [
    "standard-input register",
    "external-input boundary",
    "main theorem",
    "uniform in the cutoff",
    "uniform in the volume",
    "uniformly in the cutoff",
    "uniformly in the volume",
    "right inverse",
    "invariant graph",
    "first crossing",
    "first-crossing",
    "backward shooting",
    "Haar pivot",
    "one-pivot",
    "multipivot",
    "conditional reference",
    "replica-BKAR",
    "boundary-to-center",
    "physical exponential",
    "exponential clustering",
    "reflection positivity",
    "rotation defect",
    "dimension-four",
    "O(4)",
    "Osterwalder",
    "Hamiltonian gap",
    "nontriviality",
    "spectral mass",
    "directed subsequence",
    "directed limit",
    "continuum limit",
    "Theorem 9.3",
    "Theorem 10.2",
    "Corollary 6.11",
    "Corollary 8.12",
    "BPHZL",
    "Reisz",
    "Lüscher",
    "Weisz",
]


def pdf_text(pdf: Path) -> str:
    out = pdf.with_suffix(".txt")
    subprocess.run(["pdftotext", "-layout", str(pdf), str(out)], check=True)
    return out.read_text(encoding="utf-8", errors="replace")


def page_lines(page: str) -> list[str]:
    return [line.rstrip() for line in page.splitlines()]


def clip(lines: list[str], i: int, before: int, after: int) -> str:
    lo = max(0, i - before)
    hi = min(len(lines), i + after + 1)
    return "\n".join(lines[lo:hi]).strip()


def norm_key(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def unique_bounded(rows: list[tuple[str, str]], limit: int) -> list[tuple[str, str]]:
    seen: set[str] = set()
    out: list[tuple[str, str]] = []
    for label, text in rows:
        key = norm_key(text)
        if not key or key in seen:
            continue
        seen.add(key)
        out.append((label, text))
        if len(out) >= limit:
            break
    return out


def build_report(pdf: Path) -> str:
    raw = pdf.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    text = pdf_text(pdf)
    pages = text.split("\f")

    sections: list[tuple[str, str]] = []
    decls: list[tuple[str, str]] = []
    assumptions: list[tuple[str, str]] = []
    phrase_hits: list[tuple[str, str]] = []
    crossrefs: list[tuple[str, str]] = []

    for pageno, page in enumerate(pages, 1):
        lines = page_lines(page)
        for i, line in enumerate(lines):
            s = line.strip()
            if not s:
                continue
            if SECTION_RE.match(s):
                sections.append((f"p.{pageno}", s))
            if DECL_RE.match(s):
                decls.append((f"p.{pageno}", clip(lines, i, 0, 11)))
            low = s.lower()
            if any(k in low for k in (
                "we assume", "assume that", "assumption", "hypothesis",
                "standard input", "external input", "imported theorem",
                "we invoke", "we use the theorem", "by [",
            )):
                assumptions.append((f"p.{pageno}", clip(lines, i, 2, 8)))
            if re.search(r"\b(?:Theorem|Proposition|Lemma|Corollary)\s+[A-Z0-9.]+", s):
                crossrefs.append((f"p.{pageno}", clip(lines, i, 2, 7)))
            for phrase in PHRASES:
                if phrase.lower() in low:
                    phrase_hits.append((f"p.{pageno} · {phrase}", clip(lines, i, 3, 12)))
                    break

    sections = unique_bounded(sections, 320)
    decls = unique_bounded(decls, 260)
    assumptions = unique_bounded(assumptions, 160)
    phrase_hits = unique_bounded(phrase_hits, 260)
    crossrefs = unique_bounded(crossrefs, 180)

    parts: list[str] = [
        "# Kirk v4 bounded structural audit",
        "",
        f"- PDF bytes: `{len(raw)}`",
        f"- SHA-256: `{digest}`",
        f"- extracted pages: `{len(pages)}`",
        f"- extracted text lines: `{len(text.splitlines())}`",
        "",
        "> Bounded theorem/dependency windows only. This report is not a proof verdict and does not reproduce the manuscript.",
    ]

    def emit(title: str, rows: list[tuple[str, str]], max_chars: int = 2400) -> None:
        parts.extend(["", f"## {title}", ""])
        if not rows:
            parts.append("_No matches._")
            return
        for label, value in rows:
            parts.extend([
                f"### {label}",
                "",
                "```text",
                value[:max_chars],
                "```",
                "",
            ])

    emit("Section map", sections, 800)
    emit("Theorem / proposition / lemma / assumption windows", decls)
    emit("Explicit assumption and imported-input windows", assumptions)
    emit("Load-bearing phrase windows", phrase_hits)
    emit("Cross-reference windows", crossrefs)
    return "\n".join(parts)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pdf", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ns = ap.parse_args()
    report = build_report(ns.pdf)
    ns.out.write_text(report, encoding="utf-8")
    print(
        "KIRK_V4_STRUCTURAL_AUDIT_PASS "
        f"pdf_bytes={ns.pdf.stat().st_size} report_chars={len(report)}"
    )


if __name__ == "__main__":
    main()
