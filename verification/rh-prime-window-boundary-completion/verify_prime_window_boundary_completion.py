#!/usr/bin/env python3
"""Finite regression for the RH prime-window boundary-completion firewall.

This checks the h=1 kernel moment, its nonzero upper-boundary energy constant,
and the coherent finite square identity. It is a numerical falsifier for the
discarded boundary-completion shortcut, not a proof about primes or RH.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
from typing import Callable


def kernel(t: float) -> float:
    """The even h=1 kernel J_1 from RH-Lean PR #557."""
    z = abs(t)
    if z > 2.0:
        return 0.0
    if z <= 1.0:
        return (3.0 * z**3 - 6.0 * z**2 + 4.0) / 24.0 + (2.0 - 3.0 * z)
    return (2.0 - z) ** 3 / 24.0 - (2.0 - z)


def simpson(function: Callable[[float], float], left: float, right: float) -> float:
    midpoint = (left + right) / 2.0
    return (right - left) * (
        function(left) + 4.0 * function(midpoint) + function(right)
    ) / 6.0


def adaptive_simpson(
    function: Callable[[float], float],
    left: float,
    right: float,
    tolerance: float = 1e-12,
    depth: int = 24,
) -> float:
    whole = simpson(function, left, right)

    def recurse(a: float, b: float, estimate: float, tol: float, remaining: int) -> float:
        midpoint = (a + b) / 2.0
        lower = simpson(function, a, midpoint)
        upper = simpson(function, midpoint, b)
        refined = lower + upper
        if remaining == 0 or abs(refined - estimate) <= 15.0 * tol:
            return refined + (refined - estimate) / 15.0
        return recurse(a, midpoint, lower, tol / 2.0, remaining - 1) + recurse(
            midpoint, b, upper, tol / 2.0, remaining - 1
        )

    return recurse(left, right, whole, tolerance, depth)


def weighted_kernel_integral(left: float, right: float) -> float:
    if right <= left:
        return 0.0
    breakpoints = [left]
    for point in (-2.0, -1.0, 0.0, 1.0, 2.0):
        if left < point < right:
            breakpoints.append(point)
    breakpoints.append(right)
    return sum(
        adaptive_simpson(
            lambda t: math.exp(-t / 2.0) * kernel(t),
            a,
            b,
        )
        for a, b in zip(breakpoints, breakpoints[1:])
    )


def upper_partial(u: float) -> float:
    return weighted_kernel_integral(u - 2.0, 2.0)


def lower_partial(u: float) -> float:
    return weighted_kernel_integral(-2.0, 2.0 - u)


def boundary_constant(partial: Callable[[float], float], sign: float) -> float:
    return adaptive_simpson(
        lambda u: math.exp(sign * u) * partial(u) ** 2,
        0.0,
        4.0,
        tolerance=2e-11,
    )


def run(tolerance: float) -> dict[str, object]:
    complete_moment = weighted_kernel_integral(-2.0, 2.0)
    upper_constant = boundary_constant(upper_partial, 1.0)
    lower_constant = boundary_constant(lower_partial, -1.0)

    coherent_cases = []
    for count in (2, 3, 5, 10, 100):
        total = float(count * count)
        diagonal = float(count)
        offdiag = float(count * (count - 1))
        coherent_cases.append(
            {
                "count": count,
                "total": total,
                "diagonal": diagonal,
                "offdiagonal": offdiag,
                "identity_error": abs(total - diagonal - offdiag),
            }
        )

    result = {
        "status": "finite boundary-completion falsifier only; not RH",
        "tolerance": tolerance,
        "complete_weighted_moment": complete_moment,
        "complete_moment_zero_within_tolerance": abs(complete_moment) <= tolerance,
        "upper_boundary_energy_constant": upper_constant,
        "lower_boundary_energy_constant": lower_constant,
        "upper_boundary_constant_positive": upper_constant > 1.0,
        "lower_boundary_constant_positive": lower_constant > 0.01,
        "upper_partial_samples": {
            str(u): upper_partial(u) for u in (0.0, 0.5, 1.0, 2.0, 3.0, 3.5, 4.0)
        },
        "coherent_cases": coherent_cases,
        "all_coherent_identities_exact": all(
            case["identity_error"] == 0.0 for case in coherent_cases
        ),
    }
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tolerance", type=float, default=1e-9)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()

    result = run(arguments.tolerance)
    canonical = json.dumps(result, indent=2, sort_keys=True)
    result["certificate_sha256_without_digest_field"] = hashlib.sha256(
        canonical.encode("utf-8")
    ).hexdigest()
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if arguments.output is None:
        print(encoded, end="")
    else:
        arguments.output.write_text(encoded, encoding="utf-8")

    required = (
        result["complete_moment_zero_within_tolerance"]
        and result["upper_boundary_constant_positive"]
        and result["lower_boundary_constant_positive"]
        and result["all_coherent_identities_exact"]
    )
    if not required:
        raise SystemExit("boundary-completion finite regression failed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
