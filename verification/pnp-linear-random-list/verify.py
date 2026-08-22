#!/usr/bin/env python3
from __future__ import annotations

from decimal import Decimal, getcontext
from math import comb
import json
from pathlib import Path

getcontext().prec = 90


def log2_int(value: int) -> Decimal:
    if value <= 0:
        raise ValueError("log2_int requires a positive integer")
    return Decimal(value).ln() / Decimal(2).ln()


def circuit_log2_bound(n: int, g: int) -> Decimal:
    return (
        log2_int(g + 1)
        + log2_int(n + g + 2)
        + Decimal(g) * (Decimal(16).ln() / Decimal(2).ln() + 2 * log2_int(n + g + 2))
    )


def check_size(n: int) -> dict[str, object]:
    if n < 4096:
        raise ValueError("paper constants are stated for n >= 4096")
    g = 3 * n
    samples = 6 * n
    universe = comb(n, 4)
    exponent = n.bit_length() - 1
    if n != 1 << exponent:
        raise ValueError("finite replay sizes must be powers of two")

    log_k = circuit_log2_bound(n, g)
    log_cover = Decimal(samples) * (log2_int(2 * samples) - log2_int(universe))
    margin = -(log_k + log_cover)

    checks = {
        "quad_lower_192": 192 * universe >= n**4,
        "quad_upper_24": 24 * universe <= n**4,
        "accepted_fraction_at_most_n_minus_2": 2 * samples * n**2 <= universe,
        "circuit_log_at_most_10_n_log_n": log_k <= Decimal(10 * n * exponent),
        "cover_exponent_at_least_12_n_log_n": -log_cover >= Decimal(12 * n * exponent),
        "union_bound_strict": margin > 0,
        "false_positive_floor_144_n_minus_3": samples * n**3 >= 144 * universe,
    }
    if not all(checks.values()):
        failed = [name for name, ok in checks.items() if not ok]
        raise AssertionError(f"n={n}: failed {failed}")

    return {
        "n": n,
        "g": g,
        "samples": samples,
        "weight_four_universe": universe,
        "log2_circuit_count_upper": str(log_k.quantize(Decimal("0.000001"))),
        "log2_cover_probability_upper": str(log_cover.quantize(Decimal("0.000001"))),
        "log2_union_bound_margin": str(margin.quantize(Decimal("0.000001"))),
        "checks": checks,
    }


def check_cly_ledger(c: int, q: int) -> dict[str, object]:
    if c <= 0 or q <= 0:
        raise ValueError("c and q must be positive")
    log2_n = 2 * c * q
    n = 1 << log2_n
    padded_length = q**5
    replacement_budget = 1 << (c * q)
    samples = 6 * n
    checks = {
        "budget_squared_equals_n": replacement_budget**2 == n,
        "samples_exceed_budget": samples > replacement_budget,
        "explicit_index_bits_exceed_budget": samples * log2_n > replacement_budget,
    }
    if not all(checks.values()):
        raise AssertionError((c, q, checks))
    return {
        "c": c,
        "q": q,
        "log2_n": log2_n,
        "padded_length": padded_length,
        "replacement_budget": replacement_budget,
        "samples": samples,
        "checks": checks,
    }


def main() -> None:
    size_rows = [check_size(1 << exponent) for exponent in range(12, 25)]
    cly_rows = [check_cly_ledger(c, q) for c in (2, 3, 5) for q in (1, 2, 4, 8)]
    result = {
        "status": "PASS",
        "theorem_scope": "finite regression only; universal proof is in RH-Lean research note",
        "sizes_checked": len(size_rows),
        "cly_ledgers_checked": len(cly_rows),
        "size_rows": size_rows,
        "cly_rows": cly_rows,
        "honesty": "No uniform NP list, P != NP proof, or end-to-end CLY formalization is claimed.",
    }
    out = Path(__file__).resolve().parent / "results.json"
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")

    print("PASS PNP linear random quad-list regression")
    print(f"sizes_checked={len(size_rows)}")
    print(f"cly_ledgers_checked={len(cly_rows)}")
    for row in size_rows:
        print(f"n={row['n']} margin_bits={row['log2_union_bound_margin']}")
    print("HONESTY finite regression only; no uniform hard list or P != NP proof")


if __name__ == "__main__":
    main()
