#!/usr/bin/env python3
"""Numerical screen for the localized odd-Weil sine matrix.

This is deliberately *not* interval arithmetic and creates no RH certificate.
It evaluates Suzuki's explicit screw function in IEEE double precision,
assembles the one-dimensional overlap formula by split Gauss--Legendre
quadrature, compares two quadrature orders, and prints finite Schur
approximants.  Its purposes are normalization QA and cheap falsification.
"""

from __future__ import annotations

import argparse
import math

import numpy as np
from scipy import special


def von_mangoldt_table(limit: int) -> np.ndarray:
    """Return Lambda(n) for 0 <= n <= limit, using prime-power detection."""
    values = np.zeros(limit + 1, dtype=float)
    for prime in range(2, limit + 1):
        if any(prime % divisor == 0 for divisor in range(2, math.isqrt(prime) + 1)):
            continue
        power = prime
        while power <= limit:
            values[power] = math.log(prime)
            if power > limit // prime:
                break
            power *= prime
    return values


def lerch_endpoint(t: float) -> float:
    """Compute exp(-t/2) Phi(exp(-2t),2,1/4) by a root-of-unity filter."""
    w = math.exp(-t / 2.0)

    def dilog(z: complex) -> complex:
        return complex(special.spence(1.0 - z))

    value = 4.0 * (
        dilog(w)
        - 1j * dilog(1j * w)
        - dilog(-w)
        + 1j * dilog(-1j * w)
    )
    if abs(value.imag) > 2e-11:
        raise ArithmeticError(f"unexpected Lerch-filter imaginary part {value.imag}")
    return value.real


LERCH_AT_ZERO = lerch_endpoint(0.0)


def screw_psi(t: float, mangoldt: np.ndarray) -> float:
    """Suzuki's even Psi(t) for t >= 0, in the normalization used by the note."""
    if t < 0:
        t = -t
    arch_exp = 4.0 * (math.exp(t / 2.0) + math.exp(-t / 2.0) - 2.0)
    prime_hinges = 0.0
    cutoff = min(len(mangoldt) - 1, int(math.floor(math.exp(t) * (1.0 + 2e-15))))
    for n in range(2, cutoff + 1):
        if mangoldt[n] != 0.0:
            prime_hinges += mangoldt[n] / math.sqrt(n) * (t - math.log(n))
    linear = 0.5 * t * (float(special.digamma(0.25)) - math.log(math.pi))
    lerch = 0.25 * (LERCH_AT_ZERO - lerch_endpoint(t))
    return arch_exp - prime_hinges + linear + lerch


def overlap(a: float, j: int, k: int, x: np.ndarray) -> np.ndarray:
    """Integral cos(pi*j*u/a) cos(pi*k*(u+x)/a) over the overlap interval."""
    low = np.maximum(-a, -a - x)
    high = np.minimum(a, a - x)
    alpha_j = math.pi * j / a
    alpha_k = math.pi * k / a

    def cosine_integral(freq: float, phase: np.ndarray) -> np.ndarray:
        if abs(freq) < 1e-15:
            return (high - low) * np.cos(phase)
        return (np.sin(freq * high + phase) - np.sin(freq * low + phase)) / freq

    difference = cosine_integral(alpha_j - alpha_k, -alpha_k * x)
    total = cosine_integral(alpha_j + alpha_k, alpha_k * x)
    return 0.5 * (difference + total)


def split_points(a: float, mangoldt: np.ndarray) -> list[float]:
    points = [0.0, 2.0 * a]
    for n in range(2, len(mangoldt)):
        if mangoldt[n] != 0.0:
            point = math.log(n)
            if 0.0 < point < 2.0 * a:
                points.append(point)
    return sorted(set(points))


def odd_weil_matrix(a: float, dimension: int, order: int) -> np.ndarray:
    maximum_prime_power = max(2, int(math.ceil(math.exp(2.0 * a))))
    mangoldt = von_mangoldt_table(maximum_prime_power)
    nodes_unit, weights_unit = np.polynomial.legendre.leggauss(order)
    node_chunks: list[np.ndarray] = []
    weight_chunks: list[np.ndarray] = []
    for left, right in zip(split_points(a, mangoldt)[:-1], split_points(a, mangoldt)[1:]):
        nodes = 0.5 * (right - left) * nodes_unit + 0.5 * (right + left)
        weights = 0.5 * (right - left) * weights_unit
        node_chunks.append(nodes)
        weight_chunks.append(weights)
    x = np.concatenate(node_chunks)
    weights = np.concatenate(weight_chunks)
    psi = np.array([screw_psi(float(value), mangoldt) for value in x])

    result = np.empty((dimension, dimension), dtype=float)
    for j in range(1, dimension + 1):
        for k in range(j, dimension + 1):
            folded_overlap = overlap(a, j, k, x) + overlap(a, j, k, -x)
            integral = float(np.dot(weights, psi * folded_overlap))
            value = -(math.pi**2 * j * k / a**3) * integral
            result[j - 1, k - 1] = value
            result[k - 1, j - 1] = value
    return result


def schur_complement(matrix: np.ndarray, low_dimension: int, cutoff: int) -> np.ndarray:
    truncated = matrix[:cutoff, :cutoff]
    low = truncated[:low_dimension, :low_dimension]
    coupling = truncated[:low_dimension, low_dimension:]
    high = truncated[low_dimension:, low_dimension:]
    if high.size == 0:
        return low.copy()
    return low - coupling @ np.linalg.solve(high, coupling.T)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--a", type=float, default=math.log(2.0))
    parser.add_argument("--dimension", type=int, default=16)
    parser.add_argument("--low", type=int, default=2)
    parser.add_argument("--order", type=int, default=192)
    args = parser.parse_args()
    if not (args.a > 0 and args.dimension > args.low >= 1 and args.order >= 16):
        raise SystemExit("require a>0, dimension>low>=1, and order>=16")

    coarse_order = max(16, args.order // 2)
    coarse = odd_weil_matrix(args.a, args.dimension, coarse_order)
    matrix = odd_weil_matrix(args.a, args.dimension, args.order)
    difference = np.max(np.abs(matrix - coarse))
    symmetry = np.max(np.abs(matrix - matrix.T))
    eigenvalues = np.linalg.eigvalsh(matrix)

    print("STATUS=HEURISTIC_DOUBLE_PRECISION_NOT_A_CERTIFICATE")
    print(f"a={args.a:.17g}")
    print(f"dimension={args.dimension}")
    print(f"orders={coarse_order},{args.order}")
    print(f"max_order_difference={difference:.17g}")
    print(f"max_symmetry_defect={symmetry:.17g}")
    print(f"lerch_at_zero={LERCH_AT_ZERO:.17g}")
    print(f"psi_at_zero={screw_psi(0.0, von_mangoldt_table(2)):.17g}")
    print(f"matrix_min_eigenvalue={eigenvalues[0]:.17g}")
    print(f"matrix_max_eigenvalue={eigenvalues[-1]:.17g}")
    print("diagonal=" + ",".join(f"{value:.17g}" for value in np.diag(matrix)))
    previous_schur: np.ndarray | None = None
    for cutoff in range(args.low + 1, args.dimension + 1):
        schur = schur_complement(matrix, args.low, cutoff)
        schur_eigenvalues = np.linalg.eigvalsh(schur)
        high_eigenvalue = np.linalg.eigvalsh(
            matrix[args.low:cutoff, args.low:cutoff]
        )[0]
        fields = [
            "schur",
            f"cutoff={cutoff}",
            f"min={schur_eigenvalues[0]:.17g}",
            f"max={schur_eigenvalues[-1]:.17g}",
            f"finite_high_min={high_eigenvalue:.17g}",
        ]
        if previous_schur is not None:
            step_eigenvalues = np.linalg.eigvalsh(previous_schur - schur)
            fields.extend(
                [
                    f"step_loewner_min={step_eigenvalues[0]:.17g}",
                    f"step_loewner_max={step_eigenvalues[-1]:.17g}",
                ]
            )
        print(" ".join(fields))
        previous_schur = schur


if __name__ == "__main__":
    main()
