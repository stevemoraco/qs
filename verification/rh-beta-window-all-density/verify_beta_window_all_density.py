#!/usr/bin/env python3
"""Finite falsifier for the beta-window all-density confluent-block theorem.

The human proof is analytic. This script checks the explicit parameter budget,
finite beta-window generalized Gram matrices, and the claimed uniform bound on
R_K. It does not prove an infinite theorem, any zeta geometry statement, or RH.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np


def constants(order: int) -> dict[str, float]:
    """Compute large-order constants in logarithmic coordinates."""
    m = 2 * order
    log_coefficient_constant = (
        math.log(2.0 * math.sqrt(3.0))
        + 2.0 * math.log(order)
        + (order - 1) * math.log(19.0)
    )
    coefficient_constant = math.exp(log_coefficient_constant)

    log_root_constant = (
        math.log(48.0)
        + 4.0 * math.log(order)
        + (2 * order - 2) * math.log(19.0)
    ) / m
    root_constant = math.exp(log_root_constant)
    separation_time = 36.0 * order * root_constant

    log_rho = (
        math.log(24.0)
        + math.log(float(mp.zeta(m)))
        + 4.0 * math.log(order)
        + (2 * order - 2) * math.log(19.0)
        + m * math.log(9.0)
        + math.lgamma(m + 1.0)
        - m * math.log(separation_time)
    )
    rho = math.exp(log_rho)

    log_final_prefactor = (
        m * math.log(2.0 / 9.0)
        - math.log(32.0)
        - 4.0 * math.log(order)
        - (2 * order - 2) * math.log(19.0)
    )
    final_prefactor = (
        math.exp(log_final_prefactor)
        if log_final_prefactor > math.log(np.finfo(float).tiny)
        else 0.0
    )

    return {
        "m": float(m),
        "coefficient_constant": coefficient_constant,
        "log_coefficient_constant": log_coefficient_constant,
        "root_constant": root_constant,
        "log_root_constant": log_root_constant,
        "separation_time_for_h_one": separation_time,
        "rho": rho,
        "log_rho": log_rho,
        "final_prefactor_before_exponential": final_prefactor,
        "log_final_prefactor_before_exponential": log_final_prefactor,
    }


def beta_cross_block(order: int, omega: float) -> np.ndarray:
    """Exact beta moments evaluated with high-precision hypergeometric input."""
    m = 2 * order
    block = np.empty((order, order), dtype=np.complex128)
    for left in range(order):
        for right in range(order):
            alpha = m + left + right + 1
            beta = m + 1
            value = mp.beta(alpha, beta) * mp.hyp1f1(
                alpha, alpha + beta, -1j * omega
            )
            block[left, right] = complex(value)
    return block


def carrier_frequencies(
    count: int, geometry: str, rng: np.random.Generator
) -> np.ndarray:
    if count == 1:
        return np.array([0.0])
    if geometry == "arithmetic":
        gaps = np.ones(count - 1)
    elif geometry == "alternating":
        gaps = np.array(
            [1.0 if index % 2 == 0 else 2.5 for index in range(count - 1)]
        )
    elif geometry == "random":
        gaps = 1.0 + rng.exponential(0.8, count - 1)
    else:
        raise ValueError(geometry)
    frequencies = np.concatenate(([0.0], np.cumsum(gaps)))
    return frequencies - float(np.mean(frequencies))


def normalized_beta_gram(
    order: int, observation_time: float, frequencies: np.ndarray
) -> np.ndarray:
    count = len(frequencies)
    local = beta_cross_block(order, 0.0).real
    cholesky = np.linalg.cholesky(local)
    inverse_block = np.linalg.inv(cholesky)
    inverse = np.kron(np.eye(count), inverse_block)

    gram = np.empty((count * order, count * order), dtype=np.complex128)
    for left, left_frequency in enumerate(frequencies):
        for right, right_frequency in enumerate(frequencies):
            omega = (left_frequency - right_frequency) * observation_time
            gram[
                left * order : (left + 1) * order,
                right * order : (right + 1) * order,
            ] = beta_cross_block(order, omega)
    gram = (gram + gram.conj().T) / 2.0
    normalized = inverse @ gram @ inverse.conj().T
    return (normalized + normalized.conj().T) / 2.0


def run(seed: int, tolerance: float, precision: int) -> dict[str, object]:
    mp.mp.dps = precision
    rng = np.random.default_rng(seed)

    parameter_records: list[dict[str, object]] = []
    for order in range(1, 129):
        record = constants(order)
        parameter_records.append(
            {
                "K": order,
                **record,
                "root_below_30": record["root_constant"] < 30.0,
                "rho_below_quarter": record["rho"] <= 0.25 + tolerance,
            }
        )

    gram_records: list[dict[str, object]] = []
    for order in (1, 2, 3):
        record = constants(order)
        observation_time = record["separation_time_for_h_one"]
        proved_floor = 1.0 - record["rho"]
        for count in (2, 4, 6):
            for geometry in ("arithmetic", "alternating", "random"):
                trials = 1 if geometry != "random" else 4
                for trial in range(trials):
                    frequencies = carrier_frequencies(count, geometry, rng)
                    gram = normalized_beta_gram(order, observation_time, frequencies)
                    eigenvalues = np.linalg.eigvalsh(gram)
                    margin = float(eigenvalues[0] - proved_floor)
                    gram_records.append(
                        {
                            "K": order,
                            "carrier_count": count,
                            "geometry": geometry,
                            "trial": trial,
                            "observation_time": observation_time,
                            "rho": record["rho"],
                            "proved_floor": proved_floor,
                            "minimum_generalized_eigenvalue": float(eigenvalues[0]),
                            "maximum_generalized_eigenvalue": float(eigenvalues[-1]),
                            "margin": margin,
                            "verified": margin >= -tolerance,
                        }
                    )

    return {
        "status": "finite falsification evidence only; not RH",
        "seed": seed,
        "tolerance": tolerance,
        "mpmath_decimal_precision": precision,
        "parameter_case_count": len(parameter_records),
        "gram_case_count": len(gram_records),
        "all_root_constants_below_30": all(
            record["root_below_30"] for record in parameter_records
        ),
        "all_rho_budgets_below_quarter": all(
            record["rho_below_quarter"] for record in parameter_records
        ),
        "all_beta_gram_cases_verified": all(
            record["verified"] for record in gram_records
        ),
        "maximum_root_constant": max(
            record["root_constant"] for record in parameter_records
        ),
        "maximum_rho": max(record["rho"] for record in parameter_records),
        "minimum_beta_gram_margin": min(
            record["margin"] for record in gram_records
        ),
        "parameter_records": parameter_records,
        "gram_records": gram_records,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=260812)
    parser.add_argument("--tolerance", type=float, default=1e-9)
    parser.add_argument("--precision", type=int, default=70)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()

    certificate = run(
        seed=arguments.seed,
        tolerance=arguments.tolerance,
        precision=arguments.precision,
    )
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
        certificate["all_root_constants_below_30"]
        and certificate["all_rho_budgets_below_quarter"]
        and certificate["all_beta_gram_cases_verified"]
    )
    if not required:
        raise SystemExit("a finite beta-window check failed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
