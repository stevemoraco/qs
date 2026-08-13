#!/usr/bin/env python3
"""Deterministic arithmetic audit for the linear-scrambling Gap-MCSP note.

This script checks only displayed logarithmic counting bounds. It does not
enumerate circuits or matrices and is not a proof of any circuit lower bound,
Gap-MCSP hardness, or P != NP.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path


def log2_circuit_description_count(input_bits: int, gates: int) -> float:
    """Log2 of the explicit ordered circuit-description overcount."""
    return (
        math.log2(gates + 1)
        + math.log2(input_bits + gates + 2)
        + gates * (4.0 + 2.0 * math.log2(input_bits + gates + 2))
    )


def basis_event_log2_upper(vector_dimension: int, log2_set_size: float) -> float:
    """Log2 of `(2 |B| / 2^N)^N`."""
    return vector_dimension * (1.0 + log2_set_size - vector_dimension)


def audit(min_log_n: int, max_log_n: int) -> dict[str, object]:
    rows: list[dict[str, object]] = []
    all_union_negative = True
    all_description_quarter = True

    for log_n in range(min_log_n, max_log_n + 1):
        dimension = 1 << log_n
        gate_bound = dimension * dimension // (32 * log_n)
        separator_log_count = log2_circuit_description_count(
            dimension, gate_bound
        )
        accepted_log_size = dimension / 4.0
        event_log_probability = basis_event_log2_upper(
            dimension, accepted_log_size
        )
        union_log_upper = separator_log_count + event_log_probability
        description_quarter = separator_log_count <= dimension * dimension / 4.0
        union_negative = union_log_upper < 0.0
        all_description_quarter &= description_quarter
        all_union_negative &= union_negative

        easy_counts: dict[str, object] = {}
        for beta in (0.25, 0.50, 0.75):
            threshold = max(1, int(dimension**beta))
            easy_log_count = log2_circuit_description_count(log_n, threshold)
            easy_counts[f"beta_{beta:.2f}"] = {
                "threshold": threshold,
                "log2_description_count": easy_log_count,
                "below_N_over_4": easy_log_count <= dimension / 4.0,
                "ratio_to_N": easy_log_count / dimension,
            }

        rows.append(
            {
                "log2_N": log_n,
                "N": dimension,
                "q_floor": gate_bound,
                "log2_separator_description_bound": separator_log_count,
                "separator_bound_below_N2_over_4": description_quarter,
                "log2_fixed_circuit_basis_event_bound": event_log_probability,
                "log2_union_bound": union_log_upper,
                "union_bound_strictly_below_one": union_negative,
                "easy_set_description_checks": easy_counts,
            }
        )

    return {
        "status": "finite exact-formula arithmetic audit only; not P versus NP",
        "range": {"min_log2_N": min_log_n, "max_log2_N": max_log_n},
        "all_separator_description_bounds_below_N2_over_4": (
            all_description_quarter
        ),
        "all_union_bounds_strictly_below_one": all_union_negative,
        "rows": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-log2-N", type=int, default=5)
    parser.add_argument("--max-log2-N", type=int, default=20)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()

    certificate = audit(arguments.min_log2_N, arguments.max_log2_N)
    raw = json.dumps(certificate, indent=2, sort_keys=True)
    certificate["sha256_without_digest_field"] = hashlib.sha256(
        raw.encode("utf-8")
    ).hexdigest()
    encoded = json.dumps(certificate, indent=2, sort_keys=True) + "\n"

    if arguments.output is None:
        print(encoded, end="")
    else:
        arguments.output.write_text(encoded, encoding="utf-8")

    if not certificate[
        "all_separator_description_bounds_below_N2_over_4"
    ]:
        raise SystemExit("a displayed separator-description bound failed")
    if not certificate["all_union_bounds_strictly_below_one"]:
        raise SystemExit("a displayed random-basis union bound failed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
