#!/usr/bin/env python3
"""Exact finite replay for the symmetric restriction-density barrier.

This checker verifies, over an exhaustive finite range, that every symmetric
Boolean function which remains nonconstant after all bit fixings of depth r has
both color classes of size at least C(n, floor(r/2)).  It also checks the
factor-two construction and the exact resilience of a single Hamming layer.

The script is a finite certificate checker, not a proof of the universal theorem
and not a P-versus-NP result.
"""

from __future__ import annotations

import json
from math import comb
from typing import Iterable


def is_resilient(n: int, accepted_weights: Iterable[int], r: int) -> bool:
    """Return whether every fixing of at most r variables is nonconstant."""
    accepted = set(accepted_weights)
    assert 0 <= r <= n
    assert all(0 <= weight <= n for weight in accepted)

    for fixed in range(r + 1):
        for fixed_ones in range(fixed + 1):
            fixed_zeros = fixed - fixed_ones
            low = fixed_ones
            high = n - fixed_zeros
            values = [weight in accepted for weight in range(low, high + 1)]
            if not any(values) or all(values):
                return False
    return True


def max_resilience(n: int, accepted_weights: Iterable[int]) -> int:
    """Compute the maximum bit-fixing resilience exactly."""
    accepted = tuple(accepted_weights)
    answer = -1
    for r in range(n + 1):
        if is_resilient(n, accepted, r):
            answer = r
        else:
            break
    return answer


def support_size(n: int, accepted_weights: Iterable[int]) -> int:
    return sum(comb(n, weight) for weight in set(accepted_weights))


def exhaustive_theorem_check(max_n: int = 14) -> tuple[int, int]:
    function_count = 0
    resilient_pair_count = 0

    for n in range(1, max_n + 1):
        cube_size = 1 << n
        for mask in range(1 << (n + 1)):
            accepted = {
                weight for weight in range(n + 1) if (mask >> weight) & 1
            }
            function_count += 1
            ones = support_size(n, accepted)
            zeros = cube_size - ones
            resilience = max_resilience(n, accepted)

            for r in range(resilience + 1):
                lower = comb(n, r // 2)
                assert min(ones, zeros) >= lower, {
                    "n": n,
                    "accepted_weights": sorted(accepted),
                    "r": r,
                    "ones": ones,
                    "zeros": zeros,
                    "lower": lower,
                }
                resilient_pair_count += 1

    return function_count, resilient_pair_count


def construction_check(max_n: int = 100) -> int:
    cases = 0
    for n in range(4, max_n + 1):
        for r in range(n // 2 + 1):
            t = r // 2
            accepted = {t, n - t}
            assert is_resilient(n, accepted, r), (n, r, accepted)
            assert support_size(n, accepted) <= 2 * comb(n, t)
            cases += 1
    return cases


def exact_layer_check(max_n: int = 100) -> int:
    cases = 0
    for n in range(1, max_n + 1):
        for w in range(n + 1):
            observed = max_resilience(n, {w})
            expected = min(w, n - w)
            assert observed == expected, {
                "n": n,
                "w": w,
                "observed": observed,
                "expected": expected,
            }
            cases += 1
    return cases


def central_interval_check(max_n: int = 200) -> int:
    cases = 0
    for n in range(1, max_n + 1):
        choose_row = [comb(n, k) for k in range(n + 1)]
        for r in range(n + 1):
            t = r // 2
            low = t
            high = n - r + t
            assert low <= high
            assert high <= n - t
            lower = choose_row[t]
            for k in range(low, high + 1):
                assert choose_row[k] >= lower
                cases += 1
    return cases


def main() -> None:
    functions, resilient_pairs = exhaustive_theorem_check()
    construction_cases = construction_check()
    exact_layer_cases = exact_layer_check()
    central_interval_cases = central_interval_check()

    result = {
        "status": "PASS",
        "exhaustive_max_n": 14,
        "exhaustive_symmetric_functions": functions,
        "exhaustive_resilient_function_depth_pairs": resilient_pairs,
        "construction_max_n": 100,
        "construction_cases": construction_cases,
        "exact_layer_max_n": 100,
        "exact_layer_cases": exact_layer_cases,
        "central_interval_max_n": 200,
        "central_interval_weight_cases": central_interval_cases,
    }
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
