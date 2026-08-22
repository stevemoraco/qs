#!/usr/bin/env python3
"""Finite falsification/replay for the arithmetic-grid Cauchy Gram theorem.

This script is not the proof.  It checks finite spectra against the analytic
symbol bounds, verifies the exact Cauchy determinant product numerically,
measures the failure of the absolute-coherence spectral-radius certificate,
and stress-tests the bounded-displacement perturbation floor.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from typing import Any

import numpy as np


def floor_bound(r: float) -> float:
    x = 4.0 * math.pi * r
    return x / math.expm1(x)


def ceiling_bound(r: float) -> float:
    x = 4.0 * math.pi * r
    return x / (-math.expm1(-x))


def determinant_rate(r: float) -> float:
    return math.log(math.sinh(2.0 * math.pi * r) / (2.0 * math.pi * r))


def gram_matrix(size: int, r: float, offsets: np.ndarray | None = None) -> np.ndarray:
    labels = np.arange(size, dtype=float)
    if offsets is not None:
        labels = labels + offsets
    difference = labels[None, :] - labels[:, None]
    return 2.0 * r / (2.0 * r + 1j * difference)


def absolute_coherence_matrix(size: int, r: float) -> np.ndarray:
    labels = np.arange(size, dtype=float)
    difference = np.abs(labels[None, :] - labels[:, None])
    matrix = 2.0 * r / np.sqrt(4.0 * r * r + difference * difference)
    np.fill_diagonal(matrix, 0.0)
    return matrix


def determinant_log_product(size: int, r: float) -> float:
    return sum(
        (size - distance)
        * math.log(distance * distance / (distance * distance + 4.0 * r * r))
        for distance in range(1, size)
    )


def coherence_lower_bound(size: int, r: float) -> float:
    half = size // 2
    if half == 0:
        return 0.0
    return 2.0 * r * math.log((half + 1.0 + 2.0 * r) / (1.0 + 2.0 * r))


def perturbation_error_bound(r: float, eta: float) -> float:
    if not (0.0 <= eta < 0.5):
        raise ValueError("eta must lie in [0,1/2)")
    return (4.0 * math.pi * math.pi / 3.0) * r * eta / (1.0 - 2.0 * eta)


def run_case(
    size: int,
    r: float,
    eta: float,
    trials: int,
    rng: random.Random,
    tolerance: float,
) -> dict[str, Any]:
    matrix = gram_matrix(size, r)
    eigenvalues = np.linalg.eigvalsh(matrix)
    minimum = float(eigenvalues[0])
    maximum = float(eigenvalues[-1])
    lower = floor_bound(r)
    upper = ceiling_bound(r)

    if minimum + tolerance < lower:
        raise AssertionError(("symbol lower bound failed", size, r, minimum, lower))
    if maximum - tolerance > upper:
        raise AssertionError(("symbol upper bound failed", size, r, maximum, upper))

    sign, log_determinant = np.linalg.slogdet(matrix)
    if not (abs(sign - 1.0) <= tolerance):
        raise AssertionError(("Gram determinant sign", size, r, sign))
    product_log = determinant_log_product(size, r)
    if abs(log_determinant - product_log) > 1e-7 * max(1.0, abs(product_log)):
        raise AssertionError(
            ("Cauchy determinant mismatch", size, r, log_determinant, product_log)
        )

    coherence = absolute_coherence_matrix(size, r)
    coherence_radius = float(np.linalg.eigvalsh(coherence)[-1])
    coherence_floor = coherence_lower_bound(size, r)
    if coherence_radius + tolerance < coherence_floor:
        raise AssertionError(
            ("coherence Rayleigh lower bound failed", size, r, coherence_radius, coherence_floor)
        )

    perturbation_floor = lower - perturbation_error_bound(r, eta)
    observed_perturbed_minimum = math.inf
    for _ in range(trials):
        offsets = np.array([rng.uniform(-eta, eta) for _ in range(size)])
        perturbed = gram_matrix(size, r, offsets)
        perturbed_minimum = float(np.linalg.eigvalsh(perturbed)[0])
        observed_perturbed_minimum = min(observed_perturbed_minimum, perturbed_minimum)
        if perturbed_minimum + 5e-10 < perturbation_floor:
            raise AssertionError(
                (
                    "perturbation lower bound failed",
                    size,
                    r,
                    eta,
                    perturbed_minimum,
                    perturbation_floor,
                )
            )

    return {
        "size": size,
        "r": r,
        "symbol_floor": lower,
        "observed_minimum": minimum,
        "symbol_ceiling": upper,
        "observed_maximum": maximum,
        "log_determinant": float(log_determinant),
        "log_determinant_product": product_log,
        "asymptotic_log_determinant_per_site": -determinant_rate(r),
        "observed_log_determinant_per_site": float(log_determinant / size),
        "absolute_coherence_radius": coherence_radius,
        "absolute_coherence_lower_bound": coherence_floor,
        "eta": eta,
        "perturbation_floor": perturbation_floor,
        "minimum_over_random_perturbations": observed_perturbed_minimum,
        "trials": trials,
        "verified": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sizes", default="8,24,64,128")
    parser.add_argument("--ratios", default="0.05,0.1,0.2,0.5")
    parser.add_argument("--eta", type=float, default=0.02)
    parser.add_argument("--trials", type=int, default=40)
    parser.add_argument("--seed", type=int, default=260812)
    parser.add_argument("--tolerance", type=float, default=1e-10)
    args = parser.parse_args()

    sizes = [int(value) for value in args.sizes.split(",")]
    ratios = [float(value) for value in args.ratios.split(",")]
    if any(size < 1 for size in sizes):
        raise SystemExit("all sizes must be positive")
    if any(ratio <= 0.0 for ratio in ratios):
        raise SystemExit("all ratios must be positive")
    if not (0.0 <= args.eta < 0.5):
        raise SystemExit("eta must lie in [0,1/2)")

    rng = random.Random(args.seed)
    rows = [
        run_case(size, ratio, args.eta, args.trials, rng, args.tolerance)
        for ratio in ratios
        for size in sizes
    ]
    print(json.dumps(rows, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
