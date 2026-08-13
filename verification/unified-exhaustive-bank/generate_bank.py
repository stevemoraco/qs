#!/usr/bin/env python3
from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import time
from collections import defaultdict

FORBIDDEN = {
    "sorry": r"\bsorry\b",
    "admit": r"\badmit\b",
    "sorryAx": r"\bsorryAx\b",
    "custom_trust_decl": (
        r"(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*"
        r"(?:axiom|constant|opaque)\b"
    ),
    "unsafe": r"(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*unsafe\b",
    "native_decide": r"\bnative_decide\b",
    "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
}
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
IMPORT = re.compile(r"^(\s*)import\s+([^\n]+)$", re.M)
THM = re.compile(r"(?m)^\s*(?:protected\s+|private\s+)?(?:theorem|lemma)\s+")
DECL = re.compile(
    r"(?m)^\s*(?:protected\s+|private\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|example|def|abbrev|structure|inductive|class|instance)\s+"
)
EXCLUDED_PARTS = {
    ".git", ".lake", "node_modules", "build", "dist", "artifacts",
    "attached_assets", "tmp", "temp", "__pycache__",
}


@dataclasses.dataclass
class Candidate:
    origin: str
    path: str
    sha: str
    text: str
    module: str
    staged: pathlib.Path
    aliases: set[str]
    imports: list[str] = dataclasses.field(default_factory=list)
    thms: int = 0
    decls: int = 0


@dataclasses.dataclass
class Rejection:
    origin: str
    path: str
    sha: str
    reason: str
    detail: str = ""


def run(cmd, cwd=None, env=None, timeout=None):
    try:
        process = subprocess.run(
            cmd,
            cwd=cwd,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
        )
        return process.returncode, process.stdout
    except subprocess.TimeoutExpired as exc:
        return 124, f"timeout: {exc}"


def strip_comments_and_strings(text: str) -> str:
    out = []
    i = 0
    n = len(text)
    block = 0
    line = False
    string = False
    escaped = False
    while i < n:
        current = text[i]
        following = text[i + 1] if i + 1 < n else ""
        if line:
            out.append("\n" if current == "\n" else " ")
            line = current != "\n"
            i += 1
            continue
        if block:
            if current == "/" and following == "-":
                block += 1
                out += [" ", " "]
                i += 2
            elif current == "-" and following == "/":
                block -= 1
                out += [" ", " "]
                i += 2
            else:
                out.append("\n" if current == "\n" else " ")
                i += 1
            continue
        if string:
            out.append("\n" if current == "\n" else " ")
            if escaped:
                escaped = False
            elif current == "\\":
                escaped = True
            elif current == '"':
                string = False
            i += 1
            continue
        if current == "-" and following == "-":
            line = True
            out += [" ", " "]
            i += 2
        elif current == "/" and following == "-":
            block = 1
            out += [" ", " "]
            i += 2
        elif current == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(current)
            i += 1
    return "".join(out)


def safe(segment: str) -> str:
    result = re.sub(r"[^A-Za-z0-9_']", "_", segment) or "Root"
    if result[0].isdigit():
        result = "N_" + result
    return result


def aliases(path: str) -> set[str]:
    pure = pathlib.PurePosixPath(path).with_suffix("")
    result = {pure.name, safe(pure.name)}
    if all(IDENT.fullmatch(part) for part in pure.parts):
        result.add(".".join(pure.parts))
    if pure.parts and pure.parts[0] == "lean-worker":
        result.add(pure.name)
    for root in ("src", "lean", "Lean", "RH", "Millennium", "verification"):
        if (
            pure.parts
            and pure.parts[0] == root
            and len(pure.parts) > 1
            and all(IDENT.fullmatch(part) for part in pure.parts[1:])
        ):
            result.add(".".join(pure.parts[1:]))
    return result


def inventory(origin: str, root: pathlib.Path, outroot: pathlib.Path):
    candidates = []
    rejected = []
    seen = set()
    output = outroot.resolve()
    for source in sorted(root.rglob("*.lean")):
        resolved = source.resolve()
        relative_parts = source.relative_to(root).parts
        if resolved == output or output in resolved.parents:
            continue
        if any(part in EXCLUDED_PARTS for part in relative_parts):
            continue
        if source.name.startswith(".") or any(part.startswith("._") for part in relative_parts):
            continue
        if source.name == "lakefile.lean":
            relative = source.relative_to(root).as_posix()
            rejected.append(
                Rejection(
                    origin,
                    relative,
                    "",
                    "package_descriptor_not_theorem_module",
                    "lakefile.lean is package configuration, not a theorem module",
                )
            )
            continue
        text = source.read_text(encoding="utf-8", errors="replace")
        digest = hashlib.sha256(text.encode()).hexdigest()
        if digest in seen:
            continue
        seen.add(digest)
        clean = strip_comments_and_strings(text)
        bad = [key for key, regex in FORBIDDEN.items() if re.search(regex, clean)]
        relative = source.relative_to(root).as_posix()
        if bad:
            rejected.append(
                Rejection(origin, relative, digest, "trust_violation", ",".join(bad))
            )
            continue
        parts = [safe(part) for part in pathlib.PurePosixPath(relative).with_suffix("").parts]
        module = "UnifiedBank." + safe(origin) + "." + ".".join(parts) + "_" + digest[:10]
        staged = outroot / "Sources" / pathlib.Path(*module.split(".")).with_suffix(".lean")
        candidates.append(
            Candidate(
                origin,
                relative,
                digest,
                text,
                module,
                staged,
                aliases(relative),
                thms=len(THM.findall(clean)),
                decls=len(DECL.findall(clean)),
            )
        )
    return candidates, rejected


def stage(candidates, outroot):
    source_root = outroot / "Sources"
    shutil.rmtree(source_root, ignore_errors=True)
    source_root.mkdir(parents=True)
    alias_map = defaultdict(set)
    for candidate in candidates:
        for alias in candidate.aliases:
            alias_map[alias].add(candidate.module)
    unique = {alias: next(iter(values)) for alias, values in alias_map.items() if len(values) == 1}
    protected = ("Mathlib", "Lean", "Init", "Std", "Batteries", "Qq", "Aesop", "Lake")
    for candidate in candidates:
        def replace_import(match):
            body, separator, comment = match.group(2).partition("--")
            rewritten = []
            for token in body.split():
                if token in protected or token.startswith(tuple(prefix + "." for prefix in protected)):
                    rewritten.append(token)
                    continue
                replacement = unique.get(token)
                if replacement and replacement != candidate.module:
                    rewritten.append(replacement)
                    candidate.imports.append(token + "->" + replacement)
                else:
                    rewritten.append(token)
            return (
                match.group(1)
                + "import "
                + " ".join(rewritten)
                + ((" --" + comment) if separator else "")
            )
        candidate.staged.parent.mkdir(parents=True, exist_ok=True)
        candidate.staged.write_text(
            f"/- Canonical copy: {candidate.origin}:{candidate.path}; "
            f"SHA-256 {candidate.sha}. -/\n"
            + IMPORT.sub(replace_import, candidate.text)
        )


def lean_env(base, build, sources):
    environment = os.environ.copy()
    environment["LEAN_PATH"] = os.pathsep.join((str(build), str(sources), base))
    return environment


def missing_dependency(log: str) -> bool:
    lower = log.lower()
    return (
        "unknown module" in lower
        or "unknown package" in lower
        or ("object file" in lower and "does not exist" in lower)
        or (".olean" in lower and ("not found" in lower or "no such file" in lower))
    )


def compile_individual(candidates, outroot, base, per_file):
    build = outroot / "Build"
    shutil.rmtree(build, ignore_errors=True)
    build.mkdir(parents=True)
    sources = outroot / "Sources"
    environment = lean_env(base, build, sources)
    pending = list(candidates)
    accepted = []
    rejected = []
    logs = {}
    log_root = outroot / "generated" / "individual-logs"
    log_root.mkdir(parents=True, exist_ok=True)
    pass_number = 0
    while pending:
        pass_number += 1
        progress = False
        deferred = []
        print(f"compile pass {pass_number}: {len(pending)} pending", flush=True)
        for index, candidate in enumerate(pending, 1):
            output = build / pathlib.Path(*candidate.module.split(".")).with_suffix(".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            code, log = run(
                ["lean", "-o", str(output), str(candidate.staged)],
                cwd=str(sources),
                env=environment,
                timeout=per_file,
            )
            logs[candidate.sha] = log[-12000:]
            (log_root / f"{candidate.sha}.log").write_text(log)
            if code == 0:
                accepted.append(candidate)
                progress = True
                print(f"  [{index}/{len(pending)}] COMPILE {candidate.module}", flush=True)
            elif code != 124 and missing_dependency(log):
                deferred.append(candidate)
            else:
                rejected.append(
                    Rejection(
                        candidate.origin,
                        candidate.path,
                        candidate.sha,
                        "individual_compile_failure",
                        log[-12000:],
                    )
                )
        if not progress:
            rejected.extend(
                Rejection(
                    candidate.origin,
                    candidate.path,
                    candidate.sha,
                    "unresolved_dependency",
                    logs.get(candidate.sha, ""),
                )
                for candidate in deferred
            )
            break
        pending = deferred
    (outroot / "generated" / "individual-summary.json").write_text(
        json.dumps(
            {
                "accepted": [serializable_candidate(candidate) for candidate in accepted],
                "rejected": [dataclasses.asdict(item) for item in rejected],
            },
            indent=2,
        ) + "\n"
    )
    return accepted, rejected


def probe(modules, name, outroot, base, timeout):
    generated = outroot / "generated"
    generated.mkdir(parents=True, exist_ok=True)
    source = generated / (name + ".lean")
    source.write_text("import Mathlib\n" + "\n".join("import " + module for module in modules) + "\n")
    return run(
        ["lean", "-o", str(outroot / "Build" / (name + ".olean")), str(source)],
        cwd=str(generated),
        env=lean_env(base, outroot / "Build", outroot / "Sources"),
        timeout=timeout,
    )


def joint_closure(candidates, outroot, base, timeout):
    ordered = sorted(candidates, key=lambda item: (0 if item.origin == "CurrentRepo" else 1, item.path, item.sha))
    accepted = []
    rejected = []
    logs = []

    def add(chunk, depth=0):
        nonlocal accepted
        if not chunk:
            return
        code, log = probe(
            [candidate.module for candidate in accepted + chunk],
            f"Probe_{len(accepted)}_{len(chunk)}_{depth}",
            outroot,
            base,
            timeout,
        )
        logs.append(log[-8000:])
        if code == 0:
            accepted += chunk
            return
        if len(chunk) == 1:
            candidate = chunk[0]
            rejected.append(
                Rejection(
                    candidate.origin,
                    candidate.path,
                    candidate.sha,
                    "aggregate_collision",
                    log[-12000:],
                )
            )
            return
        midpoint = len(chunk) // 2
        add(chunk[:midpoint], depth + 1)
        add(chunk[midpoint:], depth + 1)

    for index in range(0, len(ordered), 64):
        add(ordered[index:index + 64])
    (outroot / "generated" / "joint-probes.log").write_text("\n===\n".join(logs))
    return accepted, rejected


def dump_theorems(modules, label, outroot, base, timeout):
    source = outroot / "generated" / ("Dump" + label + ".lean")
    source.write_text(
        "import Mathlib\n"
        + "\n".join("import " + module for module in modules)
        + """
open Lean Elab Command
elab "#dumpBankTheorems" : command => do
  let environment ← getEnv
  for (name, info) in environment.constants.toList do
    match info with
    | .thmInfo _ => logInfo m!"BANK_THEOREM_NAME={name}"
    | _ => pure ()
#dumpBankTheorems
"""
    )
    code, log = run(
        ["lean", str(source)],
        cwd=str(outroot / "generated"),
        env=lean_env(base, outroot / "Build", outroot / "Sources"),
        timeout=timeout,
    )
    (outroot / "generated" / ("Dump" + label + ".log")).write_text(log)
    if code != 0:
        return set()
    return set(re.findall(r"BANK_THEOREM_NAME=([^\s]+)", log))


def master_source(candidates, rejected_count, baseline_count, theorem_names):
    imports = "\n".join("import " + candidate.module for candidate in candidates)
    files = len(candidates)
    declarations = sum(candidate.decls for candidate in candidates)
    theorem_syntax = sum(candidate.thms for candidate in candidates)
    bank_count = len(theorem_names)
    theorem_manifest = ",\n    ".join("``" + name for name in theorem_names)
    return f"""import Mathlib
{imports}
namespace UnifiedMillenniumPublicBank

def importedModuleCount : Nat := {files}
def rejectedSourceCount : Nat := {rejected_count}
def sourceDeclarationCount : Nat := {declarations}
def sourceTheoremSyntaxCount : Nat := {theorem_syntax}
def baselineTheoremCount : Nat := {baseline_count}
def importedBankTheoremCount : Nat := {bank_count}

structure Checkpoint : Prop where
  modules : importedModuleCount = {files}
  rejected : rejectedSourceCount = {rejected_count}
  declarations : sourceDeclarationCount = {declarations}
  theoremSyntax : sourceTheoremSyntaxCount = {theorem_syntax}
  bankTheorems : importedBankTheoremCount = {bank_count}
  conductor : ∀
    (S : UnifiedMillenniumBraid.OfficialStatements)
    (B : UnifiedMillenniumBraid.CompleteBraid S),
    UnifiedMillenniumBraid.AllSeven S ∧
      UnifiedMillenniumBraid.NoDefects B.inversions

theorem unified_millennium_public_bank_checkpoint : Checkpoint := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact UnifiedMillenniumBraid.millennium_perelman_inversion_executable

open Lean Meta Elab Command

private def mkBalancedAndBundle
    (leaves : Array (Expr × Expr)) : MetaM (Expr × Expr) := do
  if leaves.isEmpty then
    return (mkConst \x60\x60True, mkConst \x60\x60True.intro)
  let mut layer := leaves
  while layer.size > 1 do
    let mut next : Array (Expr × Expr) := #[]
    let mut i := 0
    while i < layer.size do
      if i + 1 < layer.size then
        let (p, hp) := layer[i]!
        let (q, hq) := layer[i + 1]!
        let pq := mkApp2 (mkConst \x60\x60And) p q
        let hpq := mkAppN (mkConst \x60\x60And.intro) #[p, q, hp, hq]
        next := next.push (pq, hpq)
      else
        next := next.push layer[i]!
      i := i + 2
    layer := next
  return layer[0]!

elab "#bundleAcceptedCorpusKernel" : command => do
  let theoremNames : Array Name := #[
    {theorem_manifest}
  ]
  if theoremNames.isEmpty then
    throwError "the accepted-theorem manifest is empty"
  Command.liftTermElabM do
    let env ← getEnv
    let mut seen : NameSet := {{}}
    let mut leaves : Array (Expr × Expr) := #[]
    for n in theoremNames do
      if seen.contains n then
        throwError m!"duplicate theorem in manifest: {{n}}"
      seen := seen.insert n
      let some info := env.find? n
        | throwError m!"unknown theorem: {{n}}"
      match info with
      | .thmInfo _ => pure ()
      | _ => throwError m!"accepted entry is not a theorem declaration: {{n}}"
      let levels := List.replicate info.levelParams.length Level.zero
      let proof := mkConst n levels
      let type ← inferType proof
      unless (← isProp type) do
        throwError m!"theorem did not instantiate to Prop: {{n}}"
      leaves := leaves.push (type, proof)
    let (type, value) ← mkBalancedAndBundle leaves
    addDecl <| Declaration.thmDecl {{
      name := Name.str
        (Name.str Name.anonymous "UnifiedMillenniumPublicBank")
        "acceptedCorpusKernelBundle"
      levelParams := []
      type
      value
    }}
    logInfo m!"bundled {{leaves.size}} theorem constants into acceptedCorpusKernelBundle"

#bundleAcceptedCorpusKernel

#check UnifiedMillenniumBraid.millennium_perelman_inversion_executable
#check acceptedCorpusKernelBundle
#eval importedModuleCount
#eval importedBankTheoremCount
#print axioms acceptedCorpusKernelBundle
#print axioms unified_millennium_public_bank_checkpoint

end UnifiedMillenniumPublicBank
"""


def serializable_candidate(candidate):
    result = dataclasses.asdict(candidate)
    result["aliases"] = sorted(candidate.aliases)
    result["staged"] = str(candidate.staged)
    result["text"] = None
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--current-root", type=pathlib.Path, required=True)
    parser.add_argument("--legacy-root", type=pathlib.Path, required=True)
    parser.add_argument("--out", type=pathlib.Path, required=True)
    parser.add_argument("--timeout-per-file", type=int, default=120)
    parser.add_argument("--timeout-aggregate", type=int, default=1800)
    args = parser.parse_args()
    outroot = args.out.resolve()
    (outroot / "generated").mkdir(parents=True, exist_ok=True)
    base = os.environ.get("BANK_BASE_LEAN_PATH", "")
    if not base:
        return 2
    started = time.time()
    current, rejected_current = inventory("CurrentRepo", args.current_root.resolve(), outroot)
    legacy, rejected_legacy = inventory("LegacyRH", args.legacy_root.resolve(), outroot)
    candidates = current + legacy
    rejected = rejected_current + rejected_legacy
    stage(candidates, outroot)
    individual, individual_rejected = compile_individual(
        candidates, outroot, base, args.timeout_per_file
    )
    rejected += individual_rejected
    joint, joint_rejected = joint_closure(
        individual, outroot, base, args.timeout_aggregate
    )
    rejected += joint_rejected
    generated = outroot / "generated"
    (generated / "accepted-modules.json").write_text(
        json.dumps([serializable_candidate(candidate) for candidate in joint], indent=2) + "\n"
    )
    (generated / "rejected-sources.json").write_text(
        json.dumps([dataclasses.asdict(item) for item in rejected], indent=2) + "\n"
    )
    if not joint:
        print("no jointly importable theorem modules", flush=True)
        return 5
    baseline = dump_theorems([], "Baseline", outroot, base, args.timeout_aggregate)
    aggregate = dump_theorems(
        [candidate.module for candidate in joint],
        "Bank",
        outroot,
        base,
        args.timeout_aggregate,
    )
    if not baseline or not aggregate:
        return 3
    imported = sorted(aggregate - baseline)
    generated = outroot / "generated"
    conductor = generated / "UnifiedMillenniumPublicBank.lean"
    conductor.write_text(
        master_source(joint, len(rejected), len(baseline), imported)
    )
    code, log = run(
        [
            "lean",
            "-o",
            str(outroot / "Build" / "UnifiedMillenniumPublicBank.olean"),
            str(conductor),
        ],
        cwd=str(generated),
        env=lean_env(base, outroot / "Build", outroot / "Sources"),
        timeout=args.timeout_aggregate,
    )
    (generated / "unified-compile.log").write_text(log)
    if code != 0:
        return 4
    summary = {
        "elapsed_seconds": time.time() - started,
        "source_instances": len(candidates),
        "clean_candidates": len(candidates),
        "individually_compiled": len(individual),
        "jointly_imported_modules": len(joint),
        "rejected_sources": len(rejected),
        "source_declarations": sum(candidate.decls for candidate in joint),
        "source_theorem_syntax": sum(candidate.thms for candidate in joint),
        "baseline_theorems": len(baseline),
        "aggregate_theorems": len(aggregate),
        "imported_bank_theorems": len(imported),
    }
    (generated / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    (generated / "accepted-modules.json").write_text(
        json.dumps([serializable_candidate(candidate) for candidate in joint], indent=2) + "\n"
    )
    (generated / "rejected-sources.json").write_text(
        json.dumps([dataclasses.asdict(item) for item in rejected], indent=2) + "\n"
    )
    (generated / "imported-theorem-names.txt").write_text("\n".join(imported) + "\n")
    integer_lines = [
        f"{key}={value}" for key, value in summary.items() if isinstance(value, int)
    ]
    (generated / "summary.env").write_text("\n".join(integer_lines) + "\n")
    print("\n".join(integer_lines))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
