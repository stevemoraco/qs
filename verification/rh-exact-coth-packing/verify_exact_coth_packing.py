#!/usr/bin/env python3
"""Deterministic finite falsifier for the exact coth packing selector upgrade.

The analytic theorem is infinite and is not proved by this script. The replay
checks separated finite Cauchy sums, the shifted-lattice identity at high
precision, Euclidean-slab pseudohyperbolic bounds, external Blaschke products,
and finite model-space Gram matrices for simple clustered nodes.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np


def coth(value: float) -> float:
    return 1.0 / math.tanh(value)


def exact_packing_bound(A: float, h: float) -> float:
    ratio = A / h
    return 4.0 * math.pi * ratio * coth(math.pi * ratio)


def parent_packing_bound(A: float, h: float) -> float:
    ratio = A / h
    return 4.0 + 4.0 * math.pi**2 * ratio**2


def cauchy_sum(
    real_parts: np.ndarray,
    ordinates: np.ndarray,
    x: float,
    y: float,
) -> float:
    return float(
        np.sum(
            4.0
            * real_parts**2
            / ((x + real_parts) ** 2 + (y - ordinates) ** 2)
        )
    )


def separated_ordinates(
    count: int,
    h: float,
    geometry: str,
    rng: np.random.Generator,
) -> np.ndarray:
    if count <= 1:
        return np.array([0.0])
    if geometry == "lattice":
        gaps = np.full(count - 1, h)
    elif geometry == "alternating":
        gaps = np.array(
            [h if index % 2 == 0 else 3.25 * h for index in range(count - 1)],
            dtype=float,
        )
    elif geometry == "random":
        gaps = h * (1.0 + rng.exponential(0.8, count - 1))
    else:
        raise ValueError(geometry)
    points = np.concatenate(([0.0], np.cumsum(gaps)))
    return points - float(np.mean(points))


def inverse_half_plane_coordinate(center: complex, w: complex) -> complex:
    return (center + w * center.conjugate()) / (1.0 - w)


def half_plane_blaschke(node: complex, z: complex) -> complex:
    return (z - node) / (z + node.conjugate())


def normalized_kernel_gram(nodes: list[complex]) -> np.ndarray:
    size = len(nodes)
    gram = np.empty((size, size), dtype=np.complex128)
    for row, left in enumerate(nodes):
        for column, right in enumerate(nodes):
            gram[row, column] = (
                2.0
                * math.sqrt(left.real * right.real)
                / (left + right.conjugate())
            )
    return (gram + gram.conj().T) / 2.0


def block_orthonormalized_gram(
    nodes: list[complex], cluster_slices: list[slice]
) -> np.ndarray:
    gram = normalized_kernel_gram(nodes)
    dimension = len(nodes)
    transform = np.zeros((dimension, dimension), dtype=np.complex128)
    for cluster_slice in cluster_slices:
        local = gram[cluster_slice, cluster_slice]
        cholesky = np.linalg.cholesky(local)
        inverse_adjoint = np.linalg.inv(cholesky.conj().T)
        transform[cluster_slice, cluster_slice] = inverse_adjoint
    normalized = transform.conj().T @ gram @ transform
    return (normalized + normalized.conj().T) / 2.0


def selector_constants(
    A: float,
    h: float,
    rho: float,
    sigma: float,
    K: int,
) -> dict[str, float]:
    external_scale = 2.0 * A / (1.0 - sigma)
    argument = 2.0 * math.pi * external_scale / h
    eta = argument / math.sinh(argument)
    ratio = (1.0 + rho) / (sigma - rho)
    geometric_sum = sum(ratio**order for order in range(K))
    local = (
        eta ** (-K)
        * (1.0 - sigma) ** (-2)
        * (sigma / (sigma - rho))
        * geometric_sum
    )
    sharp = local * exact_packing_bound(A, h)
    coarse = local * parent_packing_bound(A, h)
    return {
        "external_scale": external_scale,
        "eta": eta,
        "local_interpolation_constant": local,
        "sharp_selector_constant": sharp,
        "parent_selector_constant": coarse,
    }


def run(seed: int, tolerance: float, precision: int) -> dict[str, object]:
    rng = np.random.default_rng(seed)
    mp.mp.dps = precision

    packing_records: list[dict[str, object]] = []
    for ratio in (0.01, 0.05, 0.2, 1.0, 5.0, 20.0):
        h = 1.0
        A = ratio * h
        bound = exact_packing_bound(A, h)
        parent = parent_packing_bound(A, h)
        for count in (1, 2, 5, 17, 64):
            for geometry in ("lattice", "alternating", "random"):
                trials = 2 if geometry != "random" else 12
                for trial in range(trials):
                    ordinates = separated_ordinates(count, h, geometry, rng)
                    real_parts = A * (0.02 + 0.98 * rng.random(count))
                    x = A * 10.0 ** rng.uniform(-7.0, 1.0)
                    if rng.random() < 0.4:
                        y = float(ordinates[rng.integers(0, count)])
                    else:
                        y = float(
                            rng.uniform(
                                ordinates[0] - 2.0 * h,
                                ordinates[-1] + 2.0 * h,
                            )
                        )
                    observed = cauchy_sum(real_parts, ordinates, x, y)
                    packing_records.append(
                        {
                            "A_over_h": ratio,
                            "count": count,
                            "geometry": geometry,
                            "trial": trial,
                            "observed_sum": observed,
                            "sharp_bound": bound,
                            "parent_bound": parent,
                            "sharp_margin": bound - observed,
                            "sharp_below_parent": bound <= parent + tolerance,
                            "verified": observed <= bound + tolerance,
                        }
                    )

    lattice_identity_records: list[dict[str, object]] = []
    for c_over_h in (0.03, 0.2, 1.0, 4.0):
        c = mp.mpf(c_over_h)
        h_mp = mp.mpf(1)
        for delta in (0.0, 0.13, 0.37, 0.5):
            delta_mp = mp.mpf(delta)
            numerical = mp.nsum(
                lambda n: 1 / (c**2 + (n * h_mp + delta_mp) ** 2),
                [-mp.inf, mp.inf],
            )
            formula = (
                mp.pi
                / (c * h_mp)
                * mp.sinh(2 * mp.pi * c / h_mp)
                / (
                    mp.cosh(2 * mp.pi * c / h_mp)
                    - mp.cos(2 * mp.pi * delta_mp / h_mp)
                )
            )
            maximum = mp.pi / (c * h_mp) * mp.coth(mp.pi * c / h_mp)
            error = abs(numerical - formula)
            lattice_identity_records.append(
                {
                    "c_over_h": c_over_h,
                    "delta_over_h": delta,
                    "numerical_sum": float(numerical),
                    "closed_formula": float(formula),
                    "maximum_aligned_formula": float(maximum),
                    "absolute_error": float(error),
                    "formula_below_aligned_maximum": bool(
                        formula <= maximum + mp.mpf(tolerance)
                    ),
                    "verified": bool(error <= mp.mpf("1e-45")),
                }
            )

    extremal_records: list[dict[str, object]] = []
    for ratio in (0.05, 0.5, 5.0):
        A = ratio
        h = 1.0
        bound = exact_packing_bound(A, h)
        for radius in (10, 100, 1000, 10000):
            ordinates = np.arange(-radius, radius + 1, dtype=float) * h
            real_parts = np.full(len(ordinates), A)
            observed = cauchy_sum(real_parts, ordinates, A * 1e-10, 0.0)
            extremal_records.append(
                {
                    "A_over_h": ratio,
                    "lattice_radius": radius,
                    "observed_sum": observed,
                    "sharp_bound": bound,
                    "relative_gap": (bound - observed) / bound,
                    "verified": observed <= bound + tolerance,
                }
            )

    slab_records: list[dict[str, object]] = []
    for trial in range(2000):
        alpha = 10.0 ** rng.uniform(-3.0, -0.1)
        A = alpha * (1.0 + 20.0 * rng.random())
        R = A * 3.0 * rng.random()
        center_real = rng.uniform(alpha, A)
        node_real = rng.uniform(alpha, A)
        vertical = rng.uniform(-R, R)
        center = complex(center_real, 0.0)
        node = complex(node_real, vertical)
        observed = abs(half_plane_blaschke(center, node)) ** 2
        rho_sq = 1.0 - 4.0 * alpha**2 / (4.0 * A**2 + R**2)
        slab_records.append(
            {
                "trial": trial,
                "observed_pseudohyperbolic_sq": observed,
                "certified_rho_sq": rho_sq,
                "margin": rho_sq - observed,
                "verified": (
                    observed <= rho_sq + tolerance and 0.0 <= rho_sq < 1.0
                ),
            }
        )

    cluster_records: list[dict[str, object]] = []
    external_records: list[dict[str, object]] = []
    A = 1.0
    h = 6.0
    rho = 0.08
    sigma = 0.25
    for K in (1, 2, 3):
        constants = selector_constants(A, h, rho, sigma, K)
        for cluster_count in (2, 4, 7):
            for trial in range(8):
                gaps = h * (1.0 + rng.exponential(0.4, cluster_count - 1))
                ordinates = np.concatenate(([0.0], np.cumsum(gaps)))
                ordinates -= float(np.mean(ordinates))
                center_cap = A * (1.0 - rho) / (1.0 + rho)
                center_reals = rng.uniform(0.2, center_cap, cluster_count)
                centers = [
                    complex(center_reals[index], ordinates[index])
                    for index in range(cluster_count)
                ]

                nodes: list[complex] = []
                cluster_slices: list[slice] = []
                clustered_nodes: list[list[complex]] = []
                for center in centers:
                    start = len(nodes)
                    local_nodes: list[complex] = []
                    for _ in range(K):
                        radial = rho * math.sqrt(rng.random())
                        angle = rng.uniform(0.0, 2.0 * math.pi)
                        w = radial * complex(math.cos(angle), math.sin(angle))
                        node = inverse_half_plane_coordinate(center, w)
                        local_nodes.append(node)
                        nodes.append(node)
                    clustered_nodes.append(local_nodes)
                    cluster_slices.append(slice(start, len(nodes)))

                normalized = block_orthonormalized_gram(nodes, cluster_slices)
                eigenvalues = np.linalg.eigvalsh(normalized)
                lower_floor = constants["sharp_selector_constant"] ** (-2)
                upper_ceiling = constants["sharp_selector_constant"] ** 2
                cluster_records.append(
                    {
                        "K": K,
                        "cluster_count": cluster_count,
                        "trial": trial,
                        "minimum_generalized_eigenvalue": float(eigenvalues[0]),
                        "maximum_generalized_eigenvalue": float(eigenvalues[-1]),
                        "selector_lower_floor": lower_floor,
                        "selector_upper_ceiling": upper_ceiling,
                        "verified": bool(
                            eigenvalues[0] >= lower_floor - tolerance
                            and eigenvalues[-1] <= upper_ceiling + tolerance
                        ),
                    }
                )

                eta_floor = constants["eta"] ** K
                for selected, center in enumerate(centers):
                    for contour_index in range(24):
                        angle = 2.0 * math.pi * contour_index / 24.0
                        w = sigma * complex(math.cos(angle), math.sin(angle))
                        z = inverse_half_plane_coordinate(center, w)
                        product = 1.0
                        for other, local_nodes in enumerate(clustered_nodes):
                            if other == selected:
                                continue
                            for node in local_nodes:
                                product *= abs(half_plane_blaschke(node, z))
                        external_records.append(
                            {
                                "K": K,
                                "cluster_count": cluster_count,
                                "trial": trial,
                                "selected_cluster": selected,
                                "contour_index": contour_index,
                                "observed_external_product": product,
                                "eta_power_floor": eta_floor,
                                "margin": product - eta_floor,
                                "verified": product >= eta_floor - tolerance,
                            }
                        )

    certificate: dict[str, object] = {
        "status": "finite falsification evidence only; not RH",
        "seed": seed,
        "tolerance": tolerance,
        "mpmath_decimal_precision": precision,
        "packing_case_count": len(packing_records),
        "lattice_identity_case_count": len(lattice_identity_records),
        "extremal_case_count": len(extremal_records),
        "slab_case_count": len(slab_records),
        "cluster_gram_case_count": len(cluster_records),
        "external_product_case_count": len(external_records),
        "all_packing_cases_verified": all(
            record["verified"] for record in packing_records
        ),
        "all_sharp_bounds_below_parent": all(
            record["sharp_below_parent"] for record in packing_records
        ),
        "all_lattice_identities_verified": all(
            record["verified"] and record["formula_below_aligned_maximum"]
            for record in lattice_identity_records
        ),
        "all_extremal_cases_verified": all(
            record["verified"] for record in extremal_records
        ),
        "all_slab_cases_verified": all(
            record["verified"] for record in slab_records
        ),
        "all_cluster_gram_cases_verified": all(
            record["verified"] for record in cluster_records
        ),
        "all_external_product_cases_verified": all(
            record["verified"] for record in external_records
        ),
        "minimum_packing_margin": min(
            record["sharp_margin"] for record in packing_records
        ),
        "maximum_lattice_identity_error": max(
            record["absolute_error"] for record in lattice_identity_records
        ),
        "minimum_extremal_relative_gap": min(
            record["relative_gap"] for record in extremal_records
        ),
        "minimum_slab_margin": min(record["margin"] for record in slab_records),
        "minimum_cluster_eigenvalue": min(
            record["minimum_generalized_eigenvalue"]
            for record in cluster_records
        ),
        "minimum_external_product_margin": min(
            record["margin"] for record in external_records
        ),
        "packing_records": packing_records,
        "lattice_identity_records": lattice_identity_records,
        "extremal_records": extremal_records,
        "slab_records": slab_records,
        "cluster_records": cluster_records,
        "external_records": external_records,
    }
    return certificate


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=260812)
    parser.add_argument("--tolerance", type=float, default=1e-9)
    parser.add_argument("--precision", type=int, default=80)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()

    certificate = run(arguments.seed, arguments.tolerance, arguments.precision)
    encoded_without_digest = json.dumps(certificate, indent=2, sort_keys=True)
    certificate["certificate_sha256_without_digest_field"] = hashlib.sha256(
        encoded_without_digest.encode("utf-8")
    ).hexdigest()
    encoded = json.dumps(certificate, indent=2, sort_keys=True) + "\n"

    if arguments.output is None:
        print(encoded, end="")
    else:
        arguments.output.write_text(encoded, encoding="utf-8")

    flags = [
        certificate["all_packing_cases_verified"],
        certificate["all_sharp_bounds_below_parent"],
        certificate["all_lattice_identities_verified"],
        certificate["all_extremal_cases_verified"],
        certificate["all_slab_cases_verified"],
        certificate["all_cluster_gram_cases_verified"],
        certificate["all_external_product_cases_verified"],
    ]
    if not all(flags):
        raise SystemExit("a finite coth-packing or selector audit failed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
