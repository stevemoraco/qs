#!/usr/bin/env python3
"""Exact finite certificate for nested dissociated Fourier-comb identities.

This is certificate computation, not a Navier--Stokes proof.  It uses exact
integer frequency arithmetic and Fraction-valued normalized coefficients.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
from typing import Iterable

Vec = tuple[int, int, int]


def add(a: Vec, b: Vec) -> Vec:
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])


def sub(a: Vec, b: Vec) -> Vec:
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])


def neg(a: Vec) -> Vec:
    return (-a[0], -a[1], -a[2])


def maxnorm(a: Vec) -> int:
    return max(abs(a[0]), abs(a[1]), abs(a[2]))


def comb_offsets(r: int, q: int) -> list[Vec]:
    assert r >= 0 and q > 0
    return [(q * i, q * j, q * k)
            for i, j, k in product(range(-r, r + 1), repeat=3)]


def nested_product(parent: set[Vec], r: int, q: int) -> set[Vec]:
    offsets = comb_offsets(r, q)
    children = [add(p, o) for p in parent for o in offsets]
    # Exact disjoint translated copies.
    assert len(children) == len(parent) * len(offsets)
    return set(children)


def density_coefficients(support: Iterable[Vec]) -> dict[Vec, Fraction]:
    pts = list(support)
    counts = Counter(sub(a, b) for a in pts for b in pts)
    n = len(pts)
    return {freq: Fraction(count, n) for freq, count in counts.items()}


def zero_sum_triple_count(support: Iterable[Vec]) -> int:
    pts = list(support)
    point_set = set(pts)
    pair_counts = Counter(add(a, b) for a in pts for b in pts)
    return sum(count for pair_sum, count in pair_counts.items()
               if neg(pair_sum) in point_set)


def check_level(parent: set[Vec], r: int, q: int) -> tuple[set[Vec], dict]:
    w = max((maxnorm(p) for p in parent), default=0)
    assert q > 3 * w
    child = nested_product(parent, r, q)
    offsets = set(comb_offsets(r, q))

    parent_density = density_coefficients(parent)
    child_density = density_coefficients(child)
    cutoff = q - 2 * w
    low_modes = {
        f for f in set(parent_density) | set(child_density)
        if maxnorm(f) < cutoff
    }
    mismatches = {
        str(f): [str(parent_density.get(f, Fraction(0))),
                 str(child_density.get(f, Fraction(0)))]
        for f in sorted(low_modes)
        if parent_density.get(f, Fraction(0)) != child_density.get(f, Fraction(0))
    }
    assert not mismatches
    assert child_density[(0, 0, 0)] == 1

    parent_triples = zero_sum_triple_count(parent)
    comb_triples = zero_sum_triple_count(offsets)
    child_triples = zero_sum_triple_count(child)
    assert child_triples == parent_triples * comb_triples

    side = 2 * r + 1
    one_dimensional_triples = 3 * r * r + 3 * r + 1
    assert 4 * one_dimensional_triples == 3 * side * side + 1
    assert comb_triples == one_dimensional_triples ** 3

    parent_modes = len(parent)
    comb_modes = len(offsets)
    child_modes = len(child)
    parent_cubic_ratio = Fraction(parent_triples, parent_modes ** 2)
    comb_cubic_ratio = Fraction(comb_triples, comb_modes ** 2)
    child_cubic_ratio = Fraction(child_triples, child_modes ** 2)
    assert child_cubic_ratio == parent_cubic_ratio * comb_cubic_ratio
    assert comb_cubic_ratio >= Fraction(27, 64)

    return child, {
        "parent_mode_count": parent_modes,
        "comb_mode_count": comb_modes,
        "child_mode_count": child_modes,
        "parent_bandwidth_maxnorm": w,
        "spacing": q,
        "strict_low_frequency_cutoff": cutoff,
        "low_modes_checked": len(low_modes),
        "normalized_density_zero_mode": "1",
        "low_density_exactly_preserved": True,
        "zero_sum_triple_count_factorizes": True,
        "parent_zero_sum_triples": parent_triples,
        "comb_zero_sum_triples": comb_triples,
        "child_zero_sum_triples": child_triples,
        "comb_cubic_gain_ratio_to_sqrt_modes": str(comb_cubic_ratio),
        "comb_cubic_gain_ratio_floor": "27/64",
        "child_cubic_gain_ratio_to_sqrt_modes": str(child_cubic_ratio),
        "normalized_peak_gain_squared": comb_modes,
    }


def main() -> None:
    support: set[Vec] = {(0, 0, 0)}
    levels = []
    for r, q in [(1, 4), (1, 16)]:
        support, receipt = check_level(support, r, q)
        levels.append(receipt)

    final_modes = len(support)
    final_triples = zero_sum_triple_count(support)
    final_ratio = Fraction(final_triples, final_modes ** 2)
    final_sqrt_modes = 27
    assert final_sqrt_modes ** 2 == final_modes
    final_cubic_integral = Fraction(final_triples,
                                    final_modes * final_sqrt_modes)

    result = {
        "status": "EXACT FINITE CERTIFICATE; NOT NAVIER-STOKES",
        "dimension": 3,
        "levels": levels,
        "final_mode_count": final_modes,
        "final_normalized_L2_squared": "1",
        "final_normalized_peak_gain_squared": final_modes,
        "final_zero_sum_triple_count": final_triples,
        "final_normalized_cubic_integral": str(final_cubic_integral),
        "final_cubic_gain_ratio_to_sqrt_modes": str(final_ratio),
        "all_assertions_passed": True,
    }
    out = Path(__file__).with_name("ns_nested_comb_exact_certificate.json")
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
