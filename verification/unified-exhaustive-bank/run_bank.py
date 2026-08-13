#!/usr/bin/env python3
"""Lake-aware hardening wrapper for `generate_bank.py`.

The base generator is kept readable and portable.  This runner makes every
Lean invocation pass through the pinned Lake package, excludes package
configuration files from the theorem-source corpus, and preserves one exact
compiler log for every rejected candidate before the master conductor is built.
"""
from __future__ import annotations

import json
import pathlib

import generate_bank


_original_run = generate_bank.run


def lake_run(cmd, cwd=None, env=None, timeout=None):
    if cmd and cmd[0] == "lean":
        cmd = ["lake", "env", "lean", *cmd[1:]]
    return _original_run(cmd, cwd=cwd, env=env, timeout=timeout)


generate_bank.run = lake_run

_original_inventory = generate_bank.inventory


def strict_inventory(origin, root, outroot):
    candidates, rejected = _original_inventory(origin, root, outroot)
    accepted = []
    for candidate in candidates:
        if pathlib.PurePosixPath(candidate.path).name == "lakefile.lean":
            rejected.append(
                generate_bank.Rejection(
                    candidate.origin,
                    candidate.path,
                    candidate.sha,
                    "package_descriptor_not_theorem_module",
                    "lakefile.lean is executable package configuration, not a theorem module",
                )
            )
        else:
            accepted.append(candidate)
    return accepted, rejected


generate_bank.inventory = strict_inventory


def compile_individual_with_logs(candidates, outroot, base, per_file):
    build = outroot / "Build"
    generate_bank.shutil.rmtree(build, ignore_errors=True)
    build.mkdir(parents=True)
    sources = outroot / "Sources"
    environment = generate_bank.lean_env(base, build, sources)
    log_root = outroot / "generated" / "individual-logs"
    log_root.mkdir(parents=True, exist_ok=True)
    pending = list(candidates)
    accepted = []
    rejected = []
    last_logs = {}
    pass_number = 0
    while pending:
        pass_number += 1
        progress = False
        deferred = []
        print(f"compile pass {pass_number}: {len(pending)} pending", flush=True)
        for index, candidate in enumerate(pending, 1):
            output = build / pathlib.Path(*candidate.module.split(".")).with_suffix(".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            code, log = lake_run(
                ["lean", "-o", str(output), str(candidate.staged)],
                cwd=str(sources),
                env=environment,
                timeout=per_file,
            )
            log_path = log_root / f"{candidate.sha}.log"
            log_path.write_text(log)
            last_logs[candidate.sha] = log[-12000:]
            if code == 0:
                accepted.append(candidate)
                progress = True
                print(
                    f"  [{index}/{len(pending)}] COMPILE {candidate.module}",
                    flush=True,
                )
            elif code != 124 and generate_bank.missing_dependency(log):
                deferred.append(candidate)
                print(
                    f"  [{index}/{len(pending)}] DEFER {candidate.module}",
                    flush=True,
                )
            else:
                rejected.append(
                    generate_bank.Rejection(
                        candidate.origin,
                        candidate.path,
                        candidate.sha,
                        "individual_compile_failure",
                        log[-12000:],
                    )
                )
                print(
                    f"  [{index}/{len(pending)}] REJECT {candidate.module} code={code}",
                    flush=True,
                )
        pending = deferred
        if not progress:
            rejected.extend(
                generate_bank.Rejection(
                    candidate.origin,
                    candidate.path,
                    candidate.sha,
                    "unresolved_dependency",
                    last_logs.get(candidate.sha, ""),
                )
                for candidate in pending
            )
            break
    (outroot / "generated" / "individual-summary.json").write_text(
        json.dumps(
            {
                "accepted": [candidate.module for candidate in accepted],
                "rejected": [
                    {
                        "origin": item.origin,
                        "path": item.path,
                        "sha": item.sha,
                        "reason": item.reason,
                        "detail": item.detail,
                    }
                    for item in rejected
                ],
            },
            indent=2,
        )
        + "\n"
    )
    return accepted, rejected


generate_bank.compile_individual = compile_individual_with_logs

raise SystemExit(generate_bank.main())
