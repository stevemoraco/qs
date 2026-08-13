#!/usr/bin/env python3
"""Reject proof holes and conclusion-carrying Lean escape hatches outside trusted challenges."""

from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

FORBIDDEN = re.compile(
    r"(?<![A-Za-z0-9_])(?:sorryAx|sorry|admit|axiom|opaque|unsafe|native_decide|Lean\.ofReduceBool)(?![A-Za-z0-9_])"
)


def erase_comments_and_strings(source: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    in_line = False
    in_string = False
    escaped = False

    while i < len(source):
        pair = source[i : i + 2]
        ch = source[i]

        if in_line:
            if ch == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue

        if block_depth:
            if pair == "/-":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            out.append("\n" if ch == "\n" else " ")
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue

        if pair == "--":
            in_line = True
            out.extend("  ")
            i += 2
        elif pair == "/-":
            block_depth = 1
            out.extend("  ")
            i += 2
        elif ch == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(ch)
            i += 1

    if block_depth or in_string:
        raise ValueError("unterminated Lean comment or string")
    return "".join(out)


def selected_files(root: Path) -> list[Path]:
    files = [root / "Zeta23.lean"]
    files.extend(sorted((root / "Zeta23").rglob("*.lean")))
    files.extend(sorted((root / "comparator").glob("Solution*.lean")))
    files.extend(sorted((root / "comparator" / "Solution").rglob("*.lean")))
    files.append(root / "comparator" / "ChallengeDeps.lean")
    files.extend(sorted((root / "comparator" / "ChallengeDeps").rglob("*.lean")))
    return sorted(set(files))


def main() -> int:
    if len(sys.argv) != 2:
        raise SystemExit("usage: scan_lean_trust.py REPOSITORY")
    root = Path(sys.argv[1]).resolve()
    files = selected_files(root)
    missing = [str(path) for path in files if not path.is_file()]
    if missing:
        raise SystemExit("missing selected source: " + ", ".join(missing))

    hits: list[str] = []
    aggregate = hashlib.sha256()
    for path in files:
        data = path.read_bytes()
        aggregate.update(path.relative_to(root).as_posix().encode())
        aggregate.update(b"\0")
        aggregate.update(data)
        clean = erase_comments_and_strings(data.decode("utf-8"))
        for match in FORBIDDEN.finditer(clean):
            line = clean.count("\n", 0, match.start()) + 1
            hits.append(f"{path.relative_to(root)}:{line}:{match.group(0)}")

    print(f"selected Lean files: {len(files)}")
    print(f"selected-source aggregate SHA-256: {aggregate.hexdigest()}")
    print("deliberate trusted challenge files excluded: comparator/Challenge*.lean")
    if hits:
        print("forbidden source tokens:")
        print("\n".join(hits))
        return 1
    print("trust scan: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
