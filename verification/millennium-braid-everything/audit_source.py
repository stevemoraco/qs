#!/usr/bin/env python3
"""Static trust-boundary audit for the generated one-file Lean bank.

This scanner removes nested Lean block comments, line comments, and string
contents before looking for proof holes and custom trust declarations.  It is
not a parser and is never used as a substitute for the Lean kernel.  Its role
is to prevent obvious trust escapes before compilation.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_line = False
    in_string = False
    escaped = False

    while i < n:
        c = text[i]
        d = text[i + 1] if i + 1 < n else ""

        if block_depth:
            if c == "/" and d == "-":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif c == "-" and d == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue

        if in_line:
            if c == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue

        if in_string:
            if escaped:
                escaped = False
                out.append(" ")
            elif c == "\\":
                escaped = True
                out.append(" ")
            elif c == '"':
                in_string = False
                out.append(" ")
            else:
                out.append("\n" if c == "\n" else " ")
            i += 1
            continue

        if c == "/" and d == "-":
            block_depth = 1
            out.extend("  ")
            i += 2
        elif c == "-" and d == "-":
            in_line = True
            out.extend("  ")
            i += 2
        elif c == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1

    if block_depth:
        raise SystemExit("unterminated Lean block comment")
    if in_string:
        raise SystemExit("unterminated Lean string")
    return "".join(out)


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {sys.argv[0]} SOURCE.lean")

    path = Path(sys.argv[1])
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    code = strip_comments_and_strings(text)

    forbidden_tokens = re.findall(
        r"\b(?:sorry|admit|sorryAx|native_decide)\b|Lean\.ofReduceBool",
        code,
    )
    forbidden_declarations = re.findall(
        r"(?m)^[ \t]*(?:axiom|opaque|unsafe)\b[^\n]*",
        code,
    )
    metavariable_commands = re.findall(r"(?m)^[ \t]*#check[ \t]+_\b", code)

    report = {
        "path": str(path),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "bytes": len(raw),
        "lines": text.count("\n"),
        "print_axioms_commands": len(
            re.findall(r"(?m)^[ \t]*#print[ \t]+axioms\b", code)
        ),
        "theorem_or_lemma_declarations": len(
            re.findall(r"(?m)^[ \t]*(?:theorem|lemma)\b", code)
        ),
        "forbidden_tokens": forbidden_tokens,
        "forbidden_declarations": forbidden_declarations,
        "metavariable_commands": metavariable_commands,
    }

    Path("source-audit.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(report, indent=2, sort_keys=True))

    expected = {
        "sha256": "0b5991423ffce0f4c55ece074d530ba0dd50c132b3de8698d3bb1de55257327c",
        "bytes": 681395,
        "lines": 9963,
        "print_axioms_commands": 832,
        "theorem_or_lemma_declarations": 496,
    }
    for key, value in expected.items():
        if report[key] != value:
            raise SystemExit(
                f"source audit mismatch for {key}: {report[key]!r} != {value!r}"
            )

    if forbidden_tokens or forbidden_declarations or metavariable_commands:
        raise SystemExit("forbidden Lean trust surface detected")

    print("source_trust_audit=PASS")


if __name__ == "__main__":
    main()
