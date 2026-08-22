#!/usr/bin/env python3
"""Replay and compare the finite log-Hardy covariance receipt."""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import subprocess
import sys
from pathlib import Path

from scipy.integrate import quad


def load_module(path: Path):
    sys.path.insert(0, str(path.parent))
    spec = importlib.util.spec_from_file_location("covariance_core_audit", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(str(path))
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--checker", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--fresh", type=Path, required=True)
    args = parser.parse_args()

    subprocess.run([
        sys.executable, str(args.checker),
        "--cutoffs", "10000,100000,1000000",
        "--gram-cutoff", "160",
        "--output", str(args.fresh),
    ], check=True)

    old = json.loads(args.receipt.read_text(encoding="utf-8"))
    new = json.loads(args.fresh.read_text(encoding="utf-8"))
    assert new["gram_residual"] <= new["gram_tolerance"]
    assert [row["cutoff"] for row in new["rows"]] == [10000, 100000, 1000000]

    for key in ("gram_energy", "cell_energy"):
        assert math.isclose(new[key], old[key], rel_tol=0.0, abs_tol=5e-13)
    for new_row, old_row in zip(new["rows"], old["rows"]):
        for key in ("energy", "diagonal", "cross", "half_log_log", "diagonal_error", "renormalized_cross"):
            assert math.isclose(new_row[key], old_row[key], rel_tol=0.0, abs_tol=5e-12)

    core = load_module(args.checker.parent / "covariance_core.py")
    for left, right in ((2.0, 3.0), (11.0, 22.0), (101.0, 160.0)):
        direct, _ = quad(lambda x: 1.0 / (x * x * math.log(x) ** 2), left, right)
        antiderivative = core.primitive(right) - core.primitive(left)
        assert math.isclose(direct, antiderivative, rel_tol=2e-12, abs_tol=2e-15)

    print("finite covariance regression passed")


if __name__ == "__main__":
    main()
