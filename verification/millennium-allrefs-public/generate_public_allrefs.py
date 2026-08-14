#!/usr/bin/env python3
"""Build a public all-ref Lean theorem inventory and executable braid.

The generated theorem count is an inventory certificate only.  Open Millennium
conclusions still require the native cut and bridge arguments exposed by the
already replayed `MillenniumGrandBraidEverythingExecutable.lean` source.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
OUT = HERE / "PublicAllRefsEverythingGenerated.lean"
REPORT = HERE / "public-allrefs-report.json"

DECL_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\n]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable)\s+)*"
    r"(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
)
NAMESPACE_RE = re.compile(r"(?m)^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$")
END_RE = re.compile(r"(?m)^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")
TRUST_RE = re.compile(
    r"(?m)^\s*(?:sorry|admit|axiom|opaque|unsafe)\b|"
    r"\bsorryAx\b|\bnative_decide\b|\bLean\.ofReduceBool\b"
)


@dataclass(frozen=True, order=True)
class Origin:
    ref: str
    path: str


def git(*args: str, binary: bool = False) -> bytes | str:
    p = subprocess.run(
        ["git", *args], cwd=ROOT, check=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )
    return p.stdout if binary else p.stdout.decode("utf-8", "surrogateescape")


def lean_string(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def refs() -> list[str]:
    raw = str(git(
        "for-each-ref", "--format=%(refname)",
        "refs/heads", "refs/remotes/origin", "refs/tags"
    ))
    ans = {line.strip() for line in raw.splitlines()
           if line.strip() and not line.endswith("/HEAD")}
    ans.add("HEAD")
    return sorted(ans)


def paths_at(ref: str):
    raw = bytes(git("ls-tree", "-r", "-z", "--full-tree", ref, binary=True))
    for row in raw.split(b"\0"):
        if not row:
            continue
        meta, raw_path = row.split(b"\t", 1)
        _mode, kind, blob = meta.decode("ascii").split()
        path = raw_path.decode("utf-8", "surrogateescape")
        if kind == "blob" and path.endswith(".lean") and not path.endswith(
            "PublicAllRefsEverythingGenerated.lean"
        ):
            yield blob, path


def qualified(text: str) -> list[tuple[str, str]]:
    events = []
    for m in NAMESPACE_RE.finditer(text):
        events.append((m.start(), "push", m.group(1)))
    for m in END_RE.finditer(text):
        events.append((m.start(), "pop", m.group(1) or ""))
    for m in DECL_RE.finditer(text):
        events.append((m.start(), "decl", m))
    events.sort(key=lambda x: x[0])

    stack: list[str] = []
    out: list[tuple[str, str]] = []
    for _pos, event, payload in events:
        if event == "push":
            stack.extend(str(payload).split("."))
        elif event == "pop":
            requested = str(payload)
            if requested:
                tail = requested.split(".")[-1]
                while stack:
                    if stack.pop() == tail:
                        break
            elif stack:
                stack.pop()
        else:
            m = payload
            kind, name = m.group(1), m.group(2)
            qname = name if "." in name or not stack else ".".join([*stack, name])
            out.append((kind, qname))
    return out


def lane(path: str, name: str) -> str:
    h = (path + " " + name).lower()
    if "navier" in h or "/ns" in h or "ns_" in h:
        return "navierStokes"
    if "yang" in h or "/ym" in h or "ym_" in h:
        return "yangMills"
    if "hodge" in h:
        return "hodge"
    if "pnp" in h or "p-vs-np" in h or "mcsp" in h:
        return "pNeNP"
    if "bsd" in h or "selmer" in h or "mordell" in h:
        return "bsd"
    if "perelman" in h or "poincare" in h or "poincar" in h:
        return "perelman"
    if "seventh" in h or "grandbraid" in h or "inversion" in h:
        return "seventhObject"
    if "riemann" in h or "zeta" in h or "/rh" in h or "rh_" in h:
        return "rh"
    return "other"


def main() -> None:
    all_refs = refs()
    origins_by_blob: dict[str, set[Origin]] = defaultdict(set)
    for ref in all_refs:
        for blob, path in paths_at(ref):
            origins_by_blob[blob].add(Origin(ref, path))

    sources = []
    records = []
    for blob in sorted(origins_by_blob):
        raw = bytes(git("cat-file", "blob", blob, binary=True))
        try:
            text = raw.decode("utf-8")
        except UnicodeDecodeError:
            text = ""
        origins = sorted(origins_by_blob[blob])
        canonical = origins[0]
        sha = hashlib.sha256(raw).hexdigest()
        decls = qualified(text)
        sources.append({
            "git_blob": blob,
            "sha256": sha,
            "canonical_ref": canonical.ref,
            "canonical_path": canonical.path,
            "origins": [{"ref": o.ref, "path": o.path} for o in origins],
            "contains_suspicious_trust_token": bool(TRUST_RE.search(text)),
            "theorem_like_count": len(decls),
        })
        for kind, name in decls:
            records.append({
                "source_sha256": sha,
                "canonical_path": canonical.path,
                "kind": kind,
                "name": name,
                "lane": lane(canonical.path, name),
            })

    if len(records) < 700:
        raise SystemExit(f"public all-ref theorem gate failed: {len(records)} < 700")

    lines = [
        "import Mathlib",
        "import MillenniumGrandBraidEverythingExecutable",
        "",
        "namespace MillenniumGrandBraidPublicAllRefs",
        "",
        "inductive Lane where",
        "  | rh | pNeNP | bsd | hodge | navierStokes | yangMills",
        "  | perelman | seventhObject | other",
        "  deriving Repr, DecidableEq",
        "",
        "structure TheoremRecord where",
        "  sourceSha256 : String",
        "  canonicalPath : String",
        "  kind : String",
        "  qualifiedName : String",
        "  lane : Lane",
        "  deriving Repr",
        "",
        "def theoremRecords : List TheoremRecord := [",
    ]
    for r in records:
        lines.append(
            "  { sourceSha256 := " + lean_string(r["source_sha256"])
            + ", canonicalPath := " + lean_string(r["canonical_path"])
            + ", kind := " + lean_string(r["kind"])
            + ", qualifiedName := " + lean_string(r["name"])
            + f", lane := .{r['lane']} }},"
        )
    lines += [
        "]",
        "",
        f"def refCount : Nat := {len(all_refs)}",
        f"def sourceBlobCount : Nat := {len(sources)}",
        f"def theoremLikeCount : Nat := {len(records)}",
        "",
        f"theorem exactRefCount : refCount = {len(all_refs)} := by rfl",
        f"theorem exactSourceBlobCount : sourceBlobCount = {len(sources)} := by rfl",
        f"theorem exactTheoremLikeCount : theoremLikeCount = {len(records)} := by rfl",
        "theorem minimumSevenHundredGate : 700 <= theoremLikeCount := by decide",
        "",
        "theorem indexedBankToTargetIffTarget (P : Prop) :",
        "    (700 <= theoremLikeCount -> P) <-> P := by",
        "  constructor",
        "  · intro h",
        "    exact h minimumSevenHundredGate",
        "  · intro h _",
        "    exact h",
        "",
        "theorem inventoryDoesNotProveArbitraryTarget :",
        "    ¬ (∀ P : Prop, 700 <= theoremLikeCount -> P) := by",
        "  intro h",
        "  exact h False minimumSevenHundredGate",
        "",
        "theorem publicAllRefsEverythingExecutable",
        "    (T : MillenniumGrandBraidAllSevenAudited.TargetInterfaces)",
        "    (C : MillenniumGrandBraidAllSevenAudited.MinimumCuts)",
        "    (Omega : Type*)",
        "    (bridges : MillenniumGrandBraidAllSevenAudited.CutToTarget T C)",
        "    (inversion :",
        "      MillenniumGrandBraidAllSevenAudited.SeventhObjectInversion Omega C) :",
        "    700 <= theoremLikeCount ∧",
        "    MillenniumGrandBraidAllSevenAudited.AllTargets T ∧",
        "    ¬ (∀ P : Prop, 700 <= theoremLikeCount -> P) := by",
        "  have h :=",
        "    MillenniumGrandBraidComposite.millennium_grand_braid_everything_executable",
        "      T C Omega bridges inversion",
        "  exact ⟨minimumSevenHundredGate, h.2.2.1,",
        "    inventoryDoesNotProveArbitraryTarget⟩",
        "",
        "#eval refCount",
        "#eval sourceBlobCount",
        "#eval theoremLikeCount",
        "#print axioms exactRefCount",
        "#print axioms exactSourceBlobCount",
        "#print axioms exactTheoremLikeCount",
        "#print axioms minimumSevenHundredGate",
        "#print axioms indexedBankToTargetIffTarget",
        "#print axioms inventoryDoesNotProveArbitraryTarget",
        "#print axioms publicAllRefsEverythingExecutable",
        "",
        "end MillenniumGrandBraidPublicAllRefs",
        "",
    ]
    OUT.write_text("\n".join(lines))
    report = {
        "schema": 1,
        "refs": all_refs,
        "ref_count": len(all_refs),
        "unique_source_blobs": len(sources),
        "theorem_like_declarations": len(records),
        "generated_sha256": hashlib.sha256(OUT.read_bytes()).hexdigest(),
        "sources": sources,
        "records": records,
    }
    REPORT.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: report[k] for k in (
        "ref_count", "unique_source_blobs", "theorem_like_declarations",
        "generated_sha256"
    )}, indent=2))


if __name__ == "__main__":
    main()
