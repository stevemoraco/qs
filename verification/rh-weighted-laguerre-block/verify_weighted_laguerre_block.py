#!/usr/bin/env python3
"""Finite falsifier for the weighted Laguerre exact-confluent block theorem.

The human theorem is analytic. This script only checks finite Gram matrices,
the exact triangular norm formula, and the displayed lower bound over a
reproducible parameter grid. It is not RH evidence.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from math import comb, factorial
from pathlib import Path

import numpy as np


def laguerre_coefficients(order: int) -> np.ndarray:
    """Coefficients of the standard L_order(x), ascending in x."""
    return np.array(
        [(-1) ** power * comb(order, power) / factorial(power)
         for power in range(order + 1)],
        dtype=np.complex128,
    )


def precompute_products(maximal_order: int) -> list[list[np.ndarray]]:
    coefficients = [laguerre_coefficients(order)
                    for order in range(maximal_order)]
    products: list[list[np.ndarray]] = [
        [np.empty(0, dtype=np.complex128) for _ in range(maximal_order)]
        for _ in range(maximal_order)
    ]
    for left in range(maximal_order):
        for right in range(maximal_order):
            convolution = np.convolve(coefficients[left], coefficients[right])
            products[left][right] = np.array(
                [convolution[degree] * factorial(degree)
                 for degree in range(len(convolution))],
                dtype=np.complex128,
            )
    return products


def cross_block(products: list[list[np.ndarray]], scaled_gap: float) -> np.ndarray:
    """Exact rational Laguerre cross Gram evaluated in complex double."""
    maximal_order = len(products)
    inverse = 1.0 / (1.0 + 1j * scaled_gap)
    powers = np.array(
        [inverse ** (degree + 1) for degree in range(2 * maximal_order - 1)],
        dtype=np.complex128,
    )
    block = np.empty((maximal_order, maximal_order), dtype=np.complex128)
    for left in range(maximal_order):
        for right in range(maximal_order):
            coefficients = products[left][right]
            block[left, right] = coefficients @ powers[: len(coefficients)]
    return block


def gram_matrix(maximal_order: int, damping: float, frequencies: np.ndarray) -> np.ndarray:
    products = precompute_products(maximal_order)
    carrier_count = len(frequencies)
    dimension = carrier_count * maximal_order
    gram = np.empty((dimension, dimension), dtype=np.complex128)
    for left, left_frequency in enumerate(frequencies):
        for right, right_frequency in enumerate(frequencies):
            scaled_gap = (left_frequency - right_frequency) / (2.0 * damping)
            gram[
                left * maximal_order : (left + 1) * maximal_order,
                right * maximal_order : (right + 1) * maximal_order,
            ] = cross_block(products, scaled_gap)
    return (gram + gram.conj().T) / 2.0


def triangular_norm_formula(maximal_order: int) -> float:
    return 1.0 / math.tan(math.pi / (4.0 * maximal_order))


def relative_defect(maximal_order: int, damping_over_spacing: float) -> float:
    return (
        2.0
        * math.pi
        * damping_over_spacing
        * (maximal_order + triangular_norm_formula(maximal_order))
    )


def carrier_frequencies(
    carrier_count: int,
    geometry: str,
    rng: np.random.Generator,
    spacing: float = 1.0,
) -> np.ndarray:
    if carrier_count == 1:
        return np.array([0.0])
    if geometry == "arithmetic":
        gaps = np.full(carrier_count - 1, spacing)
    elif geometry == "alternating":
        gaps = np.array(
            [spacing if index % 2 == 0 else 2.75 * spacing
             for index in range(carrier_count - 1)],
            dtype=float,
        )
    elif geometry == "random":
        gaps = spacing * (1.0 + rng.exponential(0.7, size=carrier_count - 1))
    else:
        raise ValueError(f"unknown geometry: {geometry}")
    frequencies = np.concatenate(([0.0], np.cumsum(gaps)))
    return frequencies - float(np.mean(frequencies))


def run(seed: int, tolerance: float) -> dict[str, object]:
    rng = np.random.default_rng(seed)
    frame_records: list[dict[str, object]] = []
    triangular_records: list[dict[str, object]] = []

    for maximal_order in range(1, 33):
        triangular = np.eye(maximal_order) + 2.0 * np.triu(
            np.ones((maximal_order, maximal_order)), 1
        )
        numerical_norm = float(np.linalg.svd(triangular, compute_uv=False)[0])
        formula = triangular_norm_formula(maximal_order)
        error = abs(numerical_norm - formula)
        triangular_records.append(
            {
                "K": maximal_order,
                "numerical_norm": numerical_norm,
                "cot_formula": formula,
                "absolute_error": error,
                "verified": error <= tolerance,
            }
        )

    for maximal_order in range(1, 9):
        threshold_ratio = 0.99 / (
            2.0
            * math.pi
            * (maximal_order + triangular_norm_formula(maximal_order))
        )
        for threshold_fraction in (0.1, 0.5, 0.9):
            damping_over_spacing = threshold_fraction * threshold_ratio
            proved_floor = 1.0 - relative_defect(
                maximal_order, damping_over_spacing
            )
            for carrier_count in (2, 5, 10):
                for geometry in ("arithmetic", "alternating", "random"):
                    trials = 1 if geometry != "random" else 6
                    for trial in range(trials):
                        frequencies = carrier_frequencies(
                            carrier_count, geometry, rng
                        )
                        gram = gram_matrix(
                            maximal_order, damping_over_spacing, frequencies
                        )
                        eigenvalues = np.linalg.eigvalsh(gram)
                        margin = float(eigenvalues[0] - proved_floor)
                        frame_records.append(
                            {
                                "K": maximal_order,
                                "threshold_fraction": threshold_fraction,
                                "a_over_h": damping_over_spacing,
                                "carrier_count": carrier_count,
                                "geometry": geometry,
                                "trial": trial,
                                "proved_floor": proved_floor,
                                "minimum_eigenvalue": float(eigenvalues[0]),
                                "maximum_eigenvalue": float(eigenvalues[-1]),
                                "margin": margin,
                                "verified": margin >= -tolerance,
                            }
                        )

    return {
        "status": "finite falsification evidence only; not RH",
        "seed": seed,
        "tolerance": tolerance,
        "frame_case_count": len(frame_records),
        "triangular_case_count": len(triangular_records),
        "minimum_frame_margin": min(record["margin"] for record in frame_records),
        "maximum_triangular_error": max(
            record["absolute_error"] for record in triangular_records
        ),
        "all_frame_cases_verified": all(
            record["verified"] for record in frame_records
        ),
        "all_triangular_cases_verified": all(
            record["verified"] for record in triangular_records
        ),
        "triangular_records": triangular_records,
        "frame_records": frame_records,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=260812)
    parser.add_argument("--tolerance", type=float, default=1e-9)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()

    certificate = run(arguments.seed, arguments.tolerance)
    encoded = json.dumps(certificate, indent=2, sort_keys=True)
    digest = hashlib.sha256(encoded.encode("utf-8")).hexdigest()
    certificate["certificate_sha256_without_digest_field"] = digest
    encoded = json.dumps(certificate, indent=2, sort_keys=True) + "\n"

    if arguments.output is None:
        print(encoded, end="")
    else:
        arguments.output.write_text(encoded, encoding="utf-8")

    if not certificate["all_frame_cases_verified"]:
        raise SystemExit("a finite frame case violated the displayed bound")
    if not certificate["all_triangular_cases_verified"]:
        raise SystemExit("a finite triangular norm case violated the formula")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
