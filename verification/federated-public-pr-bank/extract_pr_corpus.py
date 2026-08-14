#!/usr/bin/env python3
"""Materialize a SHA-deduplicated Lean corpus from every fetched public PR head.

The script never executes source text. It reads Git objects, preserves provenance,
and writes one UTF-8 file per unique Lean blob absent from the checked-out HEAD.
A conservative command-level prefilter rejects proof holes, custom trust
postulates, native/foreign execution hooks, and compile-time code execution
before the downstream Lean corpus scanner sees the source.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import pathlib
import re
import shutil
import subprocess
from dataclasses import asdict, dataclass

EXCLUDED_PARTS = {
    ".git", ".lake", "node_modules", "build", "dist", "artifacts",
    "attached_assets", "tmp", "temp", "__pycache__",
}
FORBIDDEN = {
    "proof_hole": re.compile(r"\b(?:sorry|admit|sorryAx)\b"),
    "custom_trust_declaration": re.compile(
        r"(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*(?:axiom|constant|opaque)\b"
    ),
    "unsafe_or_native_escape": re.compile(
        r"\b(?:unsafe|native_decide|Lean\.ofReduceBool|implemented_by|extern|foreign)\b"
    ),
    "compile_time_execution": re.compile(
        r"(?m)^\s*(?:#eval|#run|run_cmd\b|run_tac\b|initialize\b|elab\b)"
    ),
    "file_inclusion": re.compile(r"\b(?:include_str|include_bytes)\b"),
}


@dataclass
class Occurrence:
    ref: str
    commit: str
    path: str


@dataclass
class Materialized:
    blob: str
    sha256: str
    output: str
    byte_count: int
    theorem_syntax: int
    declaration_syntax: int
    occurrences: list[Occurrence]


def git(repo: pathlib.Path, *args: str, input_bytes: bytes | None = None) -> bytes:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        input=input_bytes,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"git {' '.join(args)} failed ({proc.returncode}): "
            + proc.stderr.decode("utf-8", errors="replace")[-4000:]
        )
    return proc.stdout


def tree_entries(repo: pathlib.Path, ref: str):
    raw = git(repo, "ls-tree", "-r", "-z", "--full-tree", ref)
    for record in raw.split(b"\0"):
        if not record:
            continue
        metadata, raw_path = record.split(b"\t", 1)
        mode, kind, blob = metadata.decode().split()
        path = raw_path.decode("utf-8", errors="surrogateescape")
        yield mode, kind, blob, path


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    block = 0
    line = False
    string = False
    escaped = False
    while i < len(text):
        c = text[i]
        n = text[i + 1] if i + 1 < len(text) else ""
        if line:
            out.append("\n" if c == "\n" else " ")
            line = c != "\n"
            i += 1
        elif block:
            if c == "/" and n == "-":
                block += 1
                out.extend((" ", " "))
                i += 2
            elif c == "-" and n == "/":
                block -= 1
                out.extend((" ", " "))
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif string:
            out.append("\n" if c == "\n" else " ")
            if escaped:
                escaped = False
            elif c == "\\":
                escaped = True
            elif c == '"':
                string = False
            i += 1
        elif c == "-" and n == "-":
            line = True
            out.extend((" ", " "))
            i += 2
        elif c == "/" and n == "-":
            block = 1
            out.extend((" ", " "))
            i += 2
        elif c == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def safe_name(path: str) -> str:
    base = pathlib.PurePosixPath(path).name
    base = re.sub(r"[^A-Za-z0-9_.-]", "_", base)
    if not base.endswith(".lean"):
        base += ".lean"
    return base


def read_blobs(repo: pathlib.Path, shas: list[str]) -> dict[str, bytes]:
    proc = subprocess.Popen(
        ["git", "-C", str(repo), "cat-file", "--batch"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert proc.stdin is not None and proc.stdout is not None
    result: dict[str, bytes] = {}
    try:
        for sha in shas:
            proc.stdin.write((sha + "\n").encode())
            proc.stdin.flush()
            header = proc.stdout.readline().decode().strip()
            parts = header.split()
            if len(parts) != 3 or parts[1] != "blob":
                raise RuntimeError(f"unexpected cat-file header for {sha}: {header!r}")
            size = int(parts[2])
            data = proc.stdout.read(size)
            newline = proc.stdout.read(1)
            if len(data) != size or newline != b"\n":
                raise RuntimeError(f"short cat-file payload for {sha}")
            result[sha] = data
    finally:
        proc.stdin.close()
        returncode = proc.wait()
        if returncode != 0:
            err = (proc.stderr.read() if proc.stderr else b"").decode(errors="replace")
            raise RuntimeError(f"git cat-file --batch failed: {err[-4000:]}")
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=pathlib.Path, required=True)
    parser.add_argument("--out", type=pathlib.Path, required=True)
    parser.add_argument("--manifest", type=pathlib.Path, required=True)
    parser.add_argument("--ref-prefix", default="refs/remotes/origin/pr/")
    args = parser.parse_args()

    repo = args.repo.resolve()
    out = args.out.resolve()
    manifest = args.manifest.resolve()
    shutil.rmtree(out, ignore_errors=True)
    out.mkdir(parents=True, exist_ok=True)
    manifest.parent.mkdir(parents=True, exist_ok=True)

    head = git(repo, "rev-parse", "HEAD").decode().strip()
    current_blobs: set[str] = set()
    for _, kind, blob, path in tree_entries(repo, head):
        if kind == "blob" and path.endswith(".lean"):
            current_blobs.add(blob)

    refs_raw = git(
        repo,
        "for-each-ref",
        "--format=%(objectname) %(refname)",
        args.ref_prefix,
    ).decode()
    refs: list[tuple[str, str]] = []
    for line in refs_raw.splitlines():
        if not line.strip():
            continue
        commit, ref = line.split(" ", 1)
        refs.append((ref, commit))
    refs.sort()

    occurrences: dict[str, list[Occurrence]] = collections.defaultdict(list)
    for ref, commit in refs:
        for _, kind, blob, path in tree_entries(repo, ref):
            parts = pathlib.PurePosixPath(path).parts
            if kind != "blob" or not path.endswith(".lean"):
                continue
            if any(part in EXCLUDED_PARTS for part in parts):
                continue
            if blob in current_blobs:
                continue
            occurrences[blob].append(Occurrence(ref=ref, commit=commit, path=path))

    blobs = read_blobs(repo, sorted(occurrences))
    accepted: list[Materialized] = []
    rejected: list[dict[str, object]] = []
    theorem_re = re.compile(r"(?m)^\s*(?:protected\s+|private\s+)?(?:theorem|lemma)\s+")
    decl_re = re.compile(
        r"(?m)^\s*(?:protected\s+|private\s+|noncomputable\s+)*"
        r"(?:theorem|lemma|example|def|abbrev|structure|inductive|class|instance)\s+"
    )

    for blob in sorted(blobs):
        data = blobs[blob]
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError as exc:
            rejected.append({"blob": blob, "reason": "non_utf8", "detail": str(exc)})
            continue
        clean = strip_comments_and_strings(text)
        violations = [name for name, pattern in FORBIDDEN.items() if pattern.search(clean)]
        if violations:
            rejected.append({
                "blob": blob,
                "reason": "prefilter_rejection",
                "detail": violations,
                "occurrences": [asdict(item) for item in occurrences[blob]],
            })
            continue
        first_path = occurrences[blob][0].path
        relative = pathlib.Path(blob[:2]) / f"{blob}_{safe_name(first_path)}"
        destination = out / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
        accepted.append(Materialized(
            blob=blob,
            sha256=hashlib.sha256(data).hexdigest(),
            output=relative.as_posix(),
            byte_count=len(data),
            theorem_syntax=len(theorem_re.findall(clean)),
            declaration_syntax=len(decl_re.findall(clean)),
            occurrences=occurrences[blob],
        ))

    payload = {
        "checked_out_head": head,
        "ref_prefix": args.ref_prefix,
        "fetched_ref_count": len(refs),
        "current_head_lean_blob_count": len(current_blobs),
        "unique_pr_only_lean_blobs": len(occurrences),
        "materialized_blobs": len(accepted),
        "prefilter_rejected_blobs": len(rejected),
        "materialized_theorem_syntax": sum(item.theorem_syntax for item in accepted),
        "materialized_declaration_syntax": sum(item.declaration_syntax for item in accepted),
        "accepted": [asdict(item) for item in accepted],
        "rejected": rejected,
    }
    manifest.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    summary = (
        f"fetched_pr_refs={len(refs)}\n"
        f"unique_pr_only_lean_blobs={len(occurrences)}\n"
        f"materialized_blobs={len(accepted)}\n"
        f"prefilter_rejected_blobs={len(rejected)}\n"
        f"materialized_theorem_syntax={payload['materialized_theorem_syntax']}\n"
        f"materialized_declaration_syntax={payload['materialized_declaration_syntax']}\n"
    )
    (manifest.parent / "federated-extraction-summary.env").write_text(summary)
    print(summary, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
