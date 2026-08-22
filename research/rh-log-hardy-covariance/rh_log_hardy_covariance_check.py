#!/usr/bin/env python3
"""Finite covariance regression only; this program does not test RH."""

from __future__ import annotations

import argparse
import json
import platform
from pathlib import Path

import numpy as np
import scipy

from covariance_core import (
    direct_gram_energy,
    exact_cell_energy,
    ledger_rows,
    mangoldt_array,
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cutoffs", default="10000,100000,1000000")
    parser.add_argument("--gram-cutoff", type=int, default=160)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    cutoffs = [int(part) for part in args.cutoffs.split(",") if part.strip()]
    rows = ledger_rows(cutoffs)

    centered = mangoldt_array(args.gram_cutoff) - 1.0
    centered[0] = 0.0
    gram = direct_gram_energy(args.gram_cutoff, centered)
    cells = exact_cell_energy(args.gram_cutoff, centered)
    residual = abs(gram - cells)
    tolerance = 5e-12 * max(1.0, abs(gram), abs(cells))
    if residual > tolerance:
        raise AssertionError((residual, tolerance))

    energies = [float(row["energy"]) for row in rows]
    if any(right + 1e-14 < left for left, right in zip(energies, energies[1:])):
        raise AssertionError("truncated energy decreased")

    receipt = {
        "status": "FINITE_FALSIFICATION_ONLY_NOT_RH",
        "weight": "1/(x^2*log(x)^2)",
        "gram_cutoff": args.gram_cutoff,
        "gram_energy": gram,
        "cell_energy": cells,
        "gram_residual": residual,
        "gram_tolerance": tolerance,
        "rows": rows,
        "python": platform.python_version(),
        "numpy": np.__version__,
        "scipy": scipy.__version__,
    }
    args.output.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
