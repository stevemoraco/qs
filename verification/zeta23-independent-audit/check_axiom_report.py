#!/usr/bin/env python3
"""Check that every printed headline and PairCeiling theorem uses only accepted Lean axioms."""

from __future__ import annotations

import re
import sys
from pathlib import Path

EXPECTED = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_REPORTS = 44


def main() -> int:
    if len(sys.argv) != 2:
        raise SystemExit("usage: check_axiom_report.py AXIOM_LOG")
    text = Path(sys.argv[1]).read_text(encoding="utf-8")
    if "declaration uses 'sorry'" in text or "sorryAx" in text:
        raise SystemExit("proof-hole dependency found in axiom replay")

    dependency_lines = [
        line.strip()
        for line in text.splitlines()
        if "depends on axioms:" in line or "does not depend on any axioms" in line
    ]
    if len(dependency_lines) != EXPECTED_REPORTS:
        raise SystemExit(
            f"expected {EXPECTED_REPORTS} theorem reports, found {len(dependency_lines)}"
        )

    bad: list[str] = []
    for line in dependency_lines:
        if "does not depend on any axioms" in line:
            continue
        match = re.search(r"depends on axioms:\s*\[([^]]*)\]\s*$", line)
        if not match:
            bad.append(line)
            continue
        actual = {item.strip() for item in match.group(1).split(",") if item.strip()}
        if not actual <= EXPECTED:
            bad.append(line)

    if bad:
        raise SystemExit("unexpected axiom reports:\n" + "\n".join(bad))

    print(f"axiom reports checked: {len(dependency_lines)}")
    print("scope: 33 comparator headlines + 11 PairCeiling reports")
    print("permitted axioms: propext, Classical.choice, Quot.sound")
    print("axiom report: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
