#!/usr/bin/env python3
"""Extract complete bounded declaration spans for named Kirk v4 results.

A span begins at the named theorem/lemma/corollary and ends immediately before
its next numbered declaration.  This is for dependency auditing, not wholesale
reproduction.
"""
from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path

START_RE = re.compile(
    r"(?m)^(?:Theorem|Lemma|Proposition|Corollary)\s+([0-9]+(?:\.[0-9]+)+)\b"
)

TARGETS = {
    "4.22", "4.30", "5.4", "5.5", "5.16", "5.17",
    "6.10", "6.11", "6.24", "6.43",
    "8.12", "8.43", "8.45", "8.46",
    "9.1", "9.2", "9.3", "10.2", "10.5",
}


def text_from_pdf(pdf: Path) -> str:
    out = pdf.with_suffix(".named.txt")
    subprocess.run(["pdftotext", "-layout", str(pdf), str(out)], check=True)
    return out.read_text(encoding="utf-8", errors="replace")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pdf", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ns = ap.parse_args()

    text = text_from_pdf(ns.pdf)
    matches = list(START_RE.finditer(text))
    found: dict[str, str] = {}
    for i, m in enumerate(matches):
        number = m.group(1)
        if number not in TARGETS:
            continue
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        span = text[m.start():end].strip()
        # Safety cap: enough for a full multi-page proof, but never a wholesale paper.
        found[number] = span[:30000]

    parts = [
        "# Kirk v4 named theorem spans",
        "",
        "> Complete declaration-to-next-declaration spans for a finite load-bearing target list. Audit use only.",
    ]
    for number in sorted(TARGETS, key=lambda s: tuple(map(int, s.split('.')))):
        parts.extend(["", f"## {number}", ""])
        span = found.get(number)
        if span is None:
            parts.append("_Not found by the declaration parser._")
        else:
            parts.extend(["```text", span, "```"])

    ns.out.write_text("\n".join(parts), encoding="utf-8")
    missing = sorted(TARGETS - found.keys())
    print(
        "KIRK_V4_NAMED_SPANS_PASS "
        f"found={len(found)} missing={','.join(missing) if missing else 'none'}"
    )


if __name__ == "__main__":
    main()
