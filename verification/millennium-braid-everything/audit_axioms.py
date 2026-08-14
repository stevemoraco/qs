#!/usr/bin/env python3
"""Audit every `#print axioms` report emitted by the one-file replay."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

EXPECTED_REPORTS = 832
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {sys.argv[0]} LEAN_OUTPUT.log")

    path = Path(sys.argv[1])
    text = path.read_text(errors="replace")
    lines = text.splitlines()

    fatal_patterns = {
        "compiler_error": r"(?m)(?:^|:) error(?:\([^)]*\))?:",
        "sorry_dependency": r"declaration uses ['`]?sorry|sorryAx",
        "metavariables": r"declaration has metavariables",
        "kernel_failure": r"kernel (?:error|exception)|unknown declaration",
    }
    fatal_hits = {
        name: re.findall(pattern, text, flags=re.IGNORECASE)
        for name, pattern in fatal_patterns.items()
    }
    fatal_hits = {name: hits for name, hits in fatal_hits.items() if hits}

    reports: list[dict[str, object]] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        no_axioms = re.match(r"^'([^']+)' does not depend on any axioms\s*$", line)
        if no_axioms:
            reports.append({"declaration": no_axioms.group(1), "axioms": []})
            i += 1
            continue

        with_axioms = re.match(r"^'([^']+)' depends on axioms:\s*(.*)$", line)
        if with_axioms:
            declaration = with_axioms.group(1)
            block = with_axioms.group(2)
            while "]" not in block:
                i += 1
                if i >= len(lines):
                    raise SystemExit(
                        f"unterminated axiom report for {declaration}"
                    )
                block += " " + lines[i].strip()
            match = re.search(r"\[(.*?)\]", block)
            if not match:
                raise SystemExit(f"unparseable axiom report for {declaration}: {block}")
            axioms = sorted(
                set(re.findall(r"[A-Za-z_][A-Za-z0-9_.]*", match.group(1)))
            )
            reports.append({"declaration": declaration, "axioms": axioms})
        i += 1

    forbidden: list[dict[str, object]] = []
    union: set[str] = set()
    for report in reports:
        axioms = set(report["axioms"])
        union.update(axioms)
        bad = sorted(axioms - ALLOWED_AXIOMS)
        if bad:
            forbidden.append(
                {"declaration": report["declaration"], "forbidden_axioms": bad}
            )

    warning_lines = [line for line in lines if "warning:" in line.lower()]
    result = {
        "expected_reports": EXPECTED_REPORTS,
        "observed_reports": len(reports),
        "unique_declarations_reported": len(
            {str(report["declaration"]) for report in reports}
        ),
        "axiom_union": sorted(union),
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "forbidden_reports": forbidden,
        "fatal_hits": fatal_hits,
        "warning_count": len(warning_lines),
        "warning_lines": warning_lines[:200],
        "reports": reports,
    }
    Path("axiom-audit.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n"
    )
    Path("axiom-union.txt").write_text("\n".join(sorted(union)) + "\n")

    summary = {key: value for key, value in result.items() if key != "reports"}
    print(json.dumps(summary, indent=2, sort_keys=True))

    if fatal_hits:
        raise SystemExit("fatal compiler/trust marker found in Lean output")
    if len(reports) != EXPECTED_REPORTS:
        raise SystemExit(
            f"axiom report count mismatch: {len(reports)} != {EXPECTED_REPORTS}"
        )
    if forbidden:
        raise SystemExit("non-foundation axiom dependency detected")

    print("axiom_audit=PASS")


if __name__ == "__main__":
    main()
