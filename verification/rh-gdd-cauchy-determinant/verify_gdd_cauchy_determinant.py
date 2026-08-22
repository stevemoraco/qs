#!/usr/bin/env python3
"""High-precision finite falsifier for the exact Hardy GDD determinant.

Finite evidence only. This does not prove the analytic theorem, zeta geometry,
or RH.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import random
from dataclasses import dataclass
from pathlib import Path

import mpmath as mp


@dataclass(frozen=True)
class Case:
    order: int
    geometry: str
    radius_fraction: float
    trial: int


def raw_gram(nodes: list[mp.mpc], a: mp.mpf) -> mp.matrix:
    """Conjugate-linear-first Gram convention."""
    K = len(nodes)
    return mp.matrix(
        [[2 * a / (mp.conj(nodes[j]) + nodes[k]) for k in range(K)]
         for j in range(K)]
    )


def gdd_transform(nodes: list[mp.mpc], a: mp.mpf) -> mp.matrix:
    K = len(nodes)
    C = mp.matrix(K, K)
    for j in range(K):
        for k in range(K):
            C[j, k] = 0
    for column in range(K):
        scale = (-2 * a) ** column
        for row in range(column + 1):
            denominator = mp.mpc(1)
            for other in range(column + 1):
                if other != row:
                    denominator *= nodes[row] - nodes[other]
            C[row, column] = scale / denominator
    return C


def vandermonde(nodes: list[mp.mpc]) -> mp.mpc:
    value = mp.mpc(1)
    for right in range(len(nodes)):
        for left in range(right):
            value *= nodes[right] - nodes[left]
    return value


def exact_gdd_determinant(nodes: list[mp.mpc], a: mp.mpf) -> mp.mpf:
    denominator = mp.mpc(1)
    for left in nodes:
        for right in nodes:
            denominator *= left + mp.conj(right)
    return mp.re((2 * a) ** (len(nodes) ** 2) / denominator)


def determinant_lower(K: int, a: mp.mpf, r: mp.mpf) -> mp.mpf:
    return (a / (a + r)) ** (K * K)


def trace_upper(K: int, a: mp.mpf, r: mp.mpf) -> mp.mpf:
    ratio = a / (a - r)
    return mp.fsum(
        mp.binomial(2 * n, n) * ratio ** (2 * n + 1)
        for n in range(K)
    )


def relative_error(actual: mp.mpf | mp.mpc, expected: mp.mpf | mp.mpc) -> mp.mpf:
    return abs(actual - expected) / max(mp.mpf(1), abs(expected))


def geometry(case: Case, a: mp.mpf, tau: mp.mpf, rng: random.Random) -> tuple[list[mp.mpc], mp.mpf]:
    K = case.order
    r = a * mp.mpf(str(case.radius_fraction))
    if case.geometry == "random":
        deltas = []
        for _ in range(K):
            radius = r * mp.sqrt(mp.mpf(str(rng.random())))
            angle = 2 * mp.pi * mp.mpf(str(rng.random()))
            deltas.append(radius * mp.e ** (1j * angle))
    elif case.geometry == "horizontal":
        deltas = [mp.mpc(-r + 2 * r * j / max(1, K - 1), 0) for j in range(K)]
    elif case.geometry == "vertical":
        deltas = [mp.mpc(0, -r + 2 * r * j / max(1, K - 1)) for j in range(K)]
    elif case.geometry == "reflected":
        deltas = [
            (-1 if j % 2 == 0 else 1)
            * mp.mpf("0.85") * r
            * mp.e ** (1j * (mp.mpf("0.4") + j * mp.mpf("0.83")))
            for j in range(K)
        ]
    elif case.geometry == "near_collision":
        center = mp.mpf("0.37") * r * mp.e ** (1j * mp.mpf("0.71"))
        microscopic = max(mp.mpf("1e-8") * r, mp.mpf("1e-30"))
        direction = mp.e ** (1j * mp.mpf("1.17"))
        deltas = [
            center
            + microscopic * (mp.mpf(j) - mp.mpf(K - 1) / 2) * direction
            for j in range(K)
        ]
    else:
        raise ValueError(case.geometry)

    for right in range(K):
        for left in range(right):
            if deltas[right] == deltas[left]:
                deltas[right] += mp.mpc(0, mp.mpf("1e-50") * (right + 1))
    return [mp.mpc(a, tau) + delta for delta in deltas], r


def run(seed: int, precision: int, tolerance_exponent: int) -> dict[str, object]:
    mp.mp.dps = precision
    rng = random.Random(seed)
    a = mp.mpf("1.375")
    tau = mp.mpf("7.25")
    tolerance = mp.mpf(10) ** (-tolerance_exponent)
    records: list[dict[str, object]] = []

    for K in range(1, 8):
        for name in ("random", "horizontal", "vertical", "reflected", "near_collision"):
            for fraction in (0.01, 0.05, 0.25, 0.6, 0.9):
                trials = 3 if name == "random" else 1
                for trial in range(trials):
                    case = Case(K, name, fraction, trial)
                    nodes, r = geometry(case, a, tau, rng)
                    C = gdd_transform(nodes, a)
                    R = raw_gram(nodes, a)
                    G = C.transpose_conj() * R * C

                    transform_expected = (
                        (-2 * a) ** (K * (K - 1) // 2) / vandermonde(nodes)
                    )
                    transform_error = relative_error(mp.det(C), transform_expected)
                    exact_det = exact_gdd_determinant(nodes, a)
                    gram_det = mp.re(mp.det(G))
                    determinant_error = relative_error(gram_det, exact_det)
                    raw_expected = exact_det / abs(transform_expected) ** 2
                    raw_error = relative_error(mp.det(R), raw_expected)

                    values, _vectors = mp.eighe(G)
                    minimum_eigenvalue = mp.re(values[0])
                    observed_trace = mp.re(mp.fsum(G[j, j] for j in range(K)))
                    det_floor = determinant_lower(K, a, r)
                    tr_ceiling = trace_upper(K, a, r)
                    spectral_floor = det_floor / tr_ceiling ** max(0, K - 1)

                    verified = all((
                        transform_error <= tolerance,
                        raw_error <= tolerance,
                        determinant_error <= tolerance,
                        gram_det + tolerance >= det_floor,
                        observed_trace <= tr_ceiling + tolerance,
                        minimum_eigenvalue + tolerance >= spectral_floor,
                        minimum_eigenvalue > 0,
                    ))
                    records.append({
                        "K": K,
                        "geometry": name,
                        "radius_fraction": fraction,
                        "trial": trial,
                        "transform_relative_error": float(transform_error),
                        "raw_cauchy_relative_error": float(raw_error),
                        "gdd_determinant_relative_error": float(determinant_error),
                        "exact_gdd_determinant": float(exact_det),
                        "determinant_floor": float(det_floor),
                        "observed_trace": float(observed_trace),
                        "trace_ceiling": float(tr_ceiling),
                        "minimum_eigenvalue": float(minimum_eigenvalue),
                        "spectral_floor": float(spectral_floor),
                        "verified": verified,
                    })

    coalescent = []
    for K in range(1, 21):
        pascal = mp.matrix(
            [[mp.binomial(j + k, j) for k in range(K)] for j in range(K)]
        )
        determinant = mp.det(pascal)
        coalescent.append({
            "K": K,
            "pascal_determinant": float(determinant),
            "verified": abs(determinant - 1) <= tolerance,
        })

    certificate: dict[str, object] = {
        "status": "finite high-precision falsification only; not RH",
        "seed": seed,
        "decimal_precision": precision,
        "tolerance_exponent": tolerance_exponent,
        "case_count": len(records),
        "coalescent_case_count": len(coalescent),
        "all_cases_verified": all(record["verified"] for record in records),
        "all_coalescent_cases_verified": all(record["verified"] for record in coalescent),
        "maximum_transform_relative_error": max(record["transform_relative_error"] for record in records),
        "maximum_raw_cauchy_relative_error": max(record["raw_cauchy_relative_error"] for record in records),
        "maximum_gdd_determinant_relative_error": max(record["gdd_determinant_relative_error"] for record in records),
        "minimum_margin_over_spectral_floor": min(
            record["minimum_eigenvalue"] - record["spectral_floor"] for record in records
        ),
        "minimum_margin_over_determinant_floor": min(
            record["exact_gdd_determinant"] - record["determinant_floor"] for record in records
        ),
        "records": records,
        "coalescent_records": coalescent,
    }
    encoded = json.dumps(certificate, indent=2, sort_keys=True)
    certificate["certificate_sha256_without_digest_field"] = hashlib.sha256(
        encoded.encode("utf-8")
    ).hexdigest()
    return certificate


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=260812)
    parser.add_argument("--precision", type=int, default=180)
    parser.add_argument("--tolerance-exponent", type=int, default=45)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    certificate = run(args.seed, args.precision, args.tolerance_exponent)
    text = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    if not certificate["all_cases_verified"]:
        raise SystemExit("a finite GDD determinant case failed")
    if not certificate["all_coalescent_cases_verified"]:
        raise SystemExit("a coalescent Pascal determinant case failed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
