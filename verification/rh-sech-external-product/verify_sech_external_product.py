#!/usr/bin/env python3
"""Finite falsifier for the sech external-product selector sharpening.

The human theorem is analytic. This script checks finite odd-lattice products,
the old/new floor comparison, random varying-real-part cluster external
products, and finite simple-node model-space Gram matrices. It is not RH
evidence and does not prove the infinite canonical product or selector theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np


def vertical_radius(A: float, radius: float) -> float:
    return 2.0 * A * radius / (1.0 - radius * radius)


def eta_old(x: float) -> float:
    return 2.0 * x / math.sinh(2.0 * x)


def eta_sech(x: float) -> float:
    return 1.0 / math.cosh(x)


def odd_product(x: mp.mpf, truncation: int) -> mp.mpf:
    u = x / mp.pi
    product = mp.mpf(1)
    for m in range(1, truncation + 1):
        product /= 1 + 4 * u * u / (2 * m - 1) ** 2
    return product


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
    transform = np.zeros_like(gram)
    for cluster_slice in cluster_slices:
        local_gram = gram[cluster_slice, cluster_slice]
        cholesky = np.linalg.cholesky(local_gram)
        inverse_adjoint = np.linalg.inv(cholesky.conj().T)
        transform[cluster_slice, cluster_slice] = inverse_adjoint
    normalized = transform.conj().T @ gram @ transform
    return (normalized + normalized.conj().T) / 2.0


def packing_constant(A: float, h: float) -> float:
    ratio = A / h
    return 4.0 * math.pi * ratio / math.tanh(math.pi * ratio)


def interpolation_constant(
    eta: float,
    rho: float,
    sigma: float,
    K: int,
) -> float:
    ratio = (1.0 + rho) / (sigma - rho)
    geometric_sum = sum(ratio**degree for degree in range(K))
    return (
        eta ** (-K)
        * (1.0 - sigma) ** (-2)
        * (sigma / (sigma - rho))
        * geometric_sum
    )


def build_cluster_family(
    A: float,
    h: float,
    rho: float,
    K: int,
    cluster_count: int,
    rng: np.random.Generator,
) -> tuple[list[complex], list[list[complex]], list[complex], list[slice]]:
    if cluster_count == 1:
        ordinates = np.array([0.0])
    else:
        gaps = h * (1.0 + rng.exponential(0.35, cluster_count - 1))
        ordinates = np.concatenate(([0.0], np.cumsum(gaps)))
        ordinates -= float(np.mean(ordinates))

    # This cap guarantees that every point in the rho-pseudohyperbolic disk
    # has real part at most A.
    center_cap = A * (1.0 - rho) / (1.0 + rho)
    center_floor = max(1e-5 * A, 0.08 * center_cap)
    center_reals = rng.uniform(center_floor, center_cap, cluster_count)
    centers = [
        complex(center_reals[index], ordinates[index])
        for index in range(cluster_count)
    ]

    all_nodes: list[complex] = []
    clustered_nodes: list[list[complex]] = []
    cluster_slices: list[slice] = []
    for center in centers:
        start = len(all_nodes)
        local_nodes: list[complex] = []
        base_angle = rng.uniform(0.0, 2.0 * math.pi)
        for local_index in range(K):
            # Keep the simple-node Gram replay numerically resolvable. The
            # analytic theorem itself permits collisions; this finite float
            # check intentionally does not claim to test that limit.
            radial = rho * (0.55 + 0.30 * rng.random())
            angular_step = 2.0 * math.pi / K
            jitter = rng.uniform(-0.08, 0.08) * angular_step
            angle = base_angle + local_index * angular_step + jitter
            w = radial * complex(math.cos(angle), math.sin(angle))
            node = inverse_half_plane_coordinate(center, w)
            assert node.real > 0.0
            assert node.real <= A * (1.0 + 5e-13)
            local_nodes.append(node)
            all_nodes.append(node)
        clustered_nodes.append(local_nodes)
        cluster_slices.append(slice(start, len(all_nodes)))
    return centers, clustered_nodes, all_nodes, cluster_slices


def run(seed: int, tolerance: float, precision: int) -> dict[str, object]:
    rng = np.random.default_rng(seed)
    mp.mp.dps = precision

    odd_product_records: list[dict[str, object]] = []
    for x_float in (0.001, 0.01, 0.1, 0.5, 1.0, 3.0, 10.0, 30.0):
        x = mp.mpf(x_float)
        exact = 1 / mp.cosh(x)
        previous: mp.mpf | None = None
        for truncation in (1, 2, 5, 20, 100, 1000):
            finite = odd_product(x, truncation)
            monotone = previous is None or finite <= previous + mp.mpf(tolerance)
            odd_product_records.append(
                {
                    "x": x_float,
                    "truncation": truncation,
                    "finite_product": float(finite),
                    "sech_limit": float(exact),
                    "margin_above_limit": float(finite - exact),
                    "monotone_from_previous": bool(monotone),
                    "verified": bool(finite + mp.mpf(tolerance) >= exact),
                }
            )
            previous = finite

    floor_comparison_records: list[dict[str, object]] = []
    for x in np.logspace(-6.0, 2.0, 1000):
        x_mp = mp.mpf(float(x))
        old = 2 * x_mp / mp.sinh(2 * x_mp)
        new = 1 / mp.cosh(x_mp)
        ratio = new / old
        identity = mp.sinh(x_mp) / x_mp
        floor_comparison_records.append(
            {
                "x": float(x),
                "old_floor": float(old),
                "sech_floor": float(new),
                "improvement_ratio": float(ratio),
                "ratio_identity_error": float(abs(ratio - identity)),
                "verified": bool(new >= old and ratio >= 1),
            }
        )

    geometry_parameters = (
        (0.005, 0.03),
        (0.03, 0.10),
        (0.08, 0.22),
        (0.16, 0.40),
        (0.30, 0.62),
    )
    external_records: list[dict[str, object]] = []
    gram_records: list[dict[str, object]] = []
    selector_records: list[dict[str, object]] = []

    A = 1.0
    slack = 0.015
    for rho, sigma in geometry_parameters:
        budget = vertical_radius(A, sigma) + vertical_radius(A, rho)
        h = 2.0 * budget * (1.0 + slack)
        assert budget <= h / 2.0 + 1e-14
        external_scale = 2.0 * A / (1.0 - sigma)
        x = math.pi * external_scale / h
        new_eta = eta_sech(x)
        old_eta = eta_old(x)
        pack = packing_constant(A, h)

        for K in (1, 2, 3, 4):
            new_local = interpolation_constant(new_eta, rho, sigma, K)
            old_local = interpolation_constant(old_eta, rho, sigma, K)
            new_selector = pack * new_local
            old_selector = pack * old_local
            selector_records.append(
                {
                    "rho": rho,
                    "sigma": sigma,
                    "A_over_h": A / h,
                    "K": K,
                    "x": x,
                    "old_eta": old_eta,
                    "sech_eta": new_eta,
                    "old_selector_constant": old_selector,
                    "sech_selector_constant": new_selector,
                    "selector_improvement_ratio": old_selector / new_selector,
                    "predicted_ratio": (new_eta / old_eta) ** K,
                    "verified": bool(
                        new_eta >= old_eta
                        and new_selector <= old_selector * (1.0 + tolerance)
                    ),
                }
            )

            for cluster_count in (2, 5, 9):
                for trial in range(5):
                    (
                        centers,
                        clustered_nodes,
                        all_nodes,
                        cluster_slices,
                    ) = build_cluster_family(
                        A, h, rho, K, cluster_count, rng
                    )

                    # The tiniest rho case makes double-precision local Gram
                    # whitening ill-conditioned for K=3; external products are
                    # still checked there, while Gram replay starts at rho=.03.
                    if K <= 3 and rho >= 0.03:
                        normalized = block_orthonormalized_gram(
                            all_nodes, cluster_slices
                        )
                        eigenvalues = np.linalg.eigvalsh(normalized)
                        lower_floor = new_selector ** (-2)
                        upper_ceiling = new_selector**2
                        gram_records.append(
                            {
                                "rho": rho,
                                "sigma": sigma,
                                "K": K,
                                "cluster_count": cluster_count,
                                "trial": trial,
                                "minimum_generalized_eigenvalue": float(
                                    eigenvalues[0]
                                ),
                                "maximum_generalized_eigenvalue": float(
                                    eigenvalues[-1]
                                ),
                                "selector_lower_floor": lower_floor,
                                "selector_upper_ceiling": upper_ceiling,
                                "verified": bool(
                                    eigenvalues[0] >= lower_floor - tolerance
                                    and eigenvalues[-1]
                                    <= upper_ceiling + tolerance
                                ),
                            }
                        )

                    external_floor = new_eta**K
                    for selected, center in enumerate(centers):
                        for contour_index in range(32):
                            angle = 2.0 * math.pi * contour_index / 32.0
                            w = sigma * complex(
                                math.cos(angle), math.sin(angle)
                            )
                            z = inverse_half_plane_coordinate(center, w)
                            product = 1.0
                            for other, local_nodes in enumerate(clustered_nodes):
                                if other == selected:
                                    continue
                                for node in local_nodes:
                                    product *= abs(half_plane_blaschke(node, z))
                            external_records.append(
                                {
                                    "rho": rho,
                                    "sigma": sigma,
                                    "A_over_h": A / h,
                                    "K": K,
                                    "cluster_count": cluster_count,
                                    "trial": trial,
                                    "selected_cluster": selected,
                                    "contour_index": contour_index,
                                    "observed_external_product": product,
                                    "sech_power_floor": external_floor,
                                    "margin": product - external_floor,
                                    "verified": product >= external_floor - tolerance,
                                }
                            )

    certificate: dict[str, object] = {
        "status": "finite falsification evidence only; not RH",
        "seed": seed,
        "tolerance": tolerance,
        "mpmath_decimal_precision": precision,
        "odd_product_case_count": len(odd_product_records),
        "floor_comparison_case_count": len(floor_comparison_records),
        "selector_comparison_case_count": len(selector_records),
        "cluster_gram_case_count": len(gram_records),
        "external_product_case_count": len(external_records),
        "all_odd_product_cases_verified": all(
            record["verified"] and record["monotone_from_previous"]
            for record in odd_product_records
        ),
        "all_floor_comparisons_verified": all(
            record["verified"] for record in floor_comparison_records
        ),
        "all_selector_comparisons_verified": all(
            record["verified"] for record in selector_records
        ),
        "all_cluster_gram_cases_verified": all(
            record["verified"] for record in gram_records
        ),
        "all_external_product_cases_verified": all(
            record["verified"] for record in external_records
        ),
        "minimum_odd_product_margin": min(
            record["margin_above_limit"] for record in odd_product_records
        ),
        "maximum_floor_ratio_identity_error": max(
            record["ratio_identity_error"]
            for record in floor_comparison_records
        ),
        "minimum_selector_improvement_ratio": min(
            record["selector_improvement_ratio"] for record in selector_records
        ),
        "minimum_cluster_eigenvalue": min(
            record["minimum_generalized_eigenvalue"] for record in gram_records
        ),
        "minimum_external_product_margin": min(
            record["margin"] for record in external_records
        ),
        "odd_product_records": odd_product_records,
        "floor_comparison_records": floor_comparison_records,
        "selector_records": selector_records,
        "gram_records": gram_records,
        "external_records": external_records,
    }
    return certificate


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=260812)
    parser.add_argument("--tolerance", type=float, default=1e-10)
    parser.add_argument("--precision", type=int, default=90)
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

    required = (
        certificate["all_odd_product_cases_verified"]
        and certificate["all_floor_comparisons_verified"]
        and certificate["all_selector_comparisons_verified"]
        and certificate["all_cluster_gram_cases_verified"]
        and certificate["all_external_product_cases_verified"]
    )
    if not required:
        raise SystemExit("a finite sech external-product audit failed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
