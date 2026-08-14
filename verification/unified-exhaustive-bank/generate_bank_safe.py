#!/usr/bin/env python3
"""Run the federated bank generator with a syntax-safe theorem manifest.

The hosted baseline replay successfully imported 613 compatible modules and
found 5,518 theorem constants, but its final generated source failed before
kernel bundling because it emitted Lean quotation syntax for private/internal
names containing numeric name components such as `_private....0....`.

Those generated implementation theorems are not needed for the research bank.
This wrapper preserves the original inventory, compilation, collision, and
axiom logic and changes only the final manifest: retain ordinary source-level
Lean names whose dot-separated components are valid identifiers, and reject
private implementation names.  The workflow still requires at least 700
imported theorem constants and direct inclusion of the giant semantic theorem.
"""

from __future__ import annotations

import importlib.util
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
ORIGINAL = HERE / "generate_bank.py"

spec = importlib.util.spec_from_file_location("unified_generate_bank_original", ORIGINAL)
if spec is None or spec.loader is None:
    raise SystemExit(f"cannot load {ORIGINAL}")
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)

original_master_source = module.master_source
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
REQUIRED_GIANT = (
    "Millennium.UnifiedBraidLive."
    "everything_discovered_one_gigantic_runnable_statement"
)


def syntax_safe_theorem_name(name: str) -> bool:
    """Whether Lean's ``qualified.name quotation parses without escaping."""
    if name.startswith("_private."):
        return False
    components = name.split(".")
    return bool(components) and all(IDENT.fullmatch(part) for part in components)


def safe_master_source(candidates, rejected_count, baseline_count, theorem_names):
    original = list(theorem_names)
    filtered = sorted({name for name in original if syntax_safe_theorem_name(name)})
    rejected = sorted(set(original) - set(filtered))

    generated = pathlib.Path(candidates[0].staged).parents[0] if candidates else HERE
    # The durable receipt is also copied by the workflow's generated/** artifact.
    report_root = pathlib.Path(module.os.environ.get("FEDERATED_SAFE_REPORT_DIR", ""))
    if report_root:
        report_root.mkdir(parents=True, exist_ok=True)
        (report_root / "syntax-safe-theorem-manifest-report.txt").write_text(
            "original_imported_theorem_constants=" + str(len(original)) + "\n"
            "syntax_safe_theorem_constants=" + str(len(filtered)) + "\n"
            "excluded_private_or_unquotable_constants=" + str(len(rejected)) + "\n"
            "required_giant_present=" + str(REQUIRED_GIANT in filtered).lower() + "\n"
            + "\n".join("EXCLUDED " + name for name in rejected)
            + ("\n" if rejected else ""),
            encoding="utf-8",
        )

    if REQUIRED_GIANT not in filtered:
        raise RuntimeError(
            "required giant semantic theorem is absent from syntax-safe manifest"
        )
    if len(filtered) < 700:
        raise RuntimeError(
            f"syntax-safe manifest has only {len(filtered)} theorem constants"
        )
    print(
        "syntax-safe theorem manifest: "
        f"{len(filtered)} retained / {len(original)} imported; "
        f"{len(rejected)} private or unquotable excluded",
        flush=True,
    )
    return original_master_source(
        candidates,
        rejected_count,
        baseline_count,
        filtered,
    )


module.master_source = safe_master_source

if __name__ == "__main__":
    raise SystemExit(module.main())
