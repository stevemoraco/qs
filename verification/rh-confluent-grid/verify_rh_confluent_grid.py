#!/usr/bin/env python3
"""Exact and high-precision replay for the confluent arithmetic-grid block symbol.

HONESTY:
- exact symbolic checks cover only finitely many multiplicities;
- high-precision checks cover only finitely many parameter cases;
- neither computation proves an infinite theorem or RH;
- the mathematical proof is in
  scratch/rh_braid/RH_CONFLUENT_ARITHMETIC_GRID_BLOCK_SYMBOL_2026-08-12.md.
"""

from __future__ import annotations

import argparse
import json
import math
from functools import lru_cache
from typing import Any

import mpmath as mp
import numpy as np
import sympy as sp


@lru_cache(maxsize=None)
def geometric_moment(k: int, q: sp.Symbol) -> sp.Expr:
    if k == 0:
        return 1 / (1 - q)
    return sp.factor(q * sp.diff(geometric_moment(k - 1, q), q))


def predicted_moment_det(m: int, q: sp.Symbol) -> sp.Expr:
    factorial_product = sp.prod(sp.factorial(j) ** 2 for j in range(m))
    return sp.factor(
        q ** (m * (m - 1) // 2)
        * factorial_product
        / (1 - q) ** (m * m)
    )


def exact_moment_checks(max_m: int) -> list[dict[str, Any]]:
    q = sp.symbols("q")
    rows: list[dict[str, Any]] = []
    for m in range(1, max_m + 1):
        matrix = sp.Matrix(
            [[geometric_moment(i + j, q) for j in range(m)] for i in range(m)]
        )
        determinant = sp.factor(matrix.det())
        predicted = predicted_moment_det(m, q)
        ratio = sp.factor(determinant / predicted)
        if ratio != 1:
            raise AssertionError(("moment determinant mismatch", m, ratio))
        rows.append(
            {
                "m": m,
                "verified_ratio": str(ratio),
                "predicted": str(predicted),
            }
        )
    return rows


def laguerre_coefficients(p: int) -> list[mp.mpf]:
    return [
        mp.mpf((-1) ** k * math.comb(p, k)) / math.factorial(k)
        for k in range(p + 1)
    ]


def eval_poly(coefficients: list[mp.mpf], x: mp.mpf) -> mp.mpf:
    value = mp.mpf("0")
    for coefficient in reversed(coefficients):
        value = value * x + coefficient
    return value


def symbol_matrix(
    m: int, r_value: str, theta_value: str, tail_tolerance: str
) -> mp.matrix:
    r = mp.mpf(r_value)
    theta = mp.mpf(theta_value)
    tolerance = mp.mpf(tail_tolerance)
    c = 4 * mp.pi * r
    coefficients = [laguerre_coefficients(p) for p in range(m)]

    matrix = mp.matrix(m, m)
    for p in range(m):
        for q_index in range(m):
            matrix[p, q_index] = mp.mpf("0")

    n = 0
    while True:
        x = 2 * r * (theta + 2 * mp.pi * n)
        weight = c * mp.exp(-x)
        values = [eval_poly(coefficients[p], x) for p in range(m)]
        for p in range(m):
            for q_index in range(m):
                matrix[p, q_index] += weight * values[p] * values[q_index]

        safe_tail_term = weight * (1 + x) ** (2 * m - 2)
        if n >= 20 and safe_tail_term < tolerance:
            break
        n += 1
        if n > 500_000:
            raise RuntimeError(("symbol series did not converge", m, r, theta))

    return matrix


def predicted_symbol_det(m: int, r_value: str, theta_value: str) -> mp.mpf:
    r = mp.mpf(r_value)
    theta = mp.mpf(theta_value)
    c = 4 * mp.pi * r
    q = mp.exp(-c)
    return (
        (c / (1 - q)) ** (m * m)
        * mp.exp(-2 * r * m * theta - 2 * mp.pi * r * m * (m - 1))
    )


def explicit_bounds(m: int, r_value: str) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    r = mp.mpf(r_value)
    c = 4 * mp.pi * r
    q = mp.exp(-c)
    s = 2 * m - 2
    trace_bound = (
        c
        * m
        * (1 + c) ** s
        * mp.factorial(s)
        / (1 - q) ** (s + 1)
    )
    determinant_floor = (
        (c / (1 - q)) ** (m * m) * q ** (m * (m + 1) / 2)
    )
    if m == 1:
        eigenvalue_floor = determinant_floor
    else:
        eigenvalue_floor = determinant_floor * (
            mp.mpf(m - 1) / trace_bound
        ) ** (m - 1)
    return determinant_floor, trace_bound, eigenvalue_floor


def gram_block_entry(p: int, q_index: int, distance: int, r_value: float) -> complex:
    """Exact finite polynomial/Laplace formula for one block coefficient."""
    z = 1 + 1j * distance / (2 * r_value)
    total = 0j
    for u in range(p + 1):
        a = ((-1) ** u) * math.comb(p, u) / math.factorial(u)
        for v in range(q_index + 1):
            b = ((-1) ** v) * math.comb(q_index, v) / math.factorial(v)
            total += a * b * math.factorial(u + v) / z ** (u + v + 1)
    return total


def finite_gram(J: int, m: int, r_value: float) -> np.ndarray:
    size = J * m
    matrix = np.empty((size, size), dtype=np.complex128)
    for j in range(J):
        for k in range(J):
            distance = k - j
            for p in range(m):
                for q_index in range(m):
                    matrix[j * m + p, k * m + q_index] = gram_block_entry(
                        p, q_index, distance, r_value
                    )
    hermitian_error = float(np.max(np.abs(matrix - matrix.conj().T)))
    if hermitian_error > 5e-12:
        raise AssertionError(("finite Gram not Hermitian", J, m, r_value, hermitian_error))
    return (matrix + matrix.conj().T) / 2


def run_numeric_cases(
    multiplicities: list[int],
    ratios: list[str],
    thetas: list[str],
    section_lengths: list[int],
    tail_tolerance: str,
) -> dict[str, Any]:
    symbol_rows: list[dict[str, Any]] = []
    section_rows: list[dict[str, Any]] = []
    max_relative_det_error = mp.mpf("0")

    for m in multiplicities:
        for r in ratios:
            determinant_floor, trace_bound, eigenvalue_floor = explicit_bounds(m, r)
            for theta in thetas:
                matrix = symbol_matrix(m, r, theta, tail_tolerance)
                observed_det = mp.det(matrix)
                predicted_det = predicted_symbol_det(m, r, theta)
                relative_error = abs(observed_det / predicted_det - 1)
                max_relative_det_error = max(max_relative_det_error, relative_error)
                if relative_error > mp.mpf("1e-45"):
                    raise AssertionError(
                        ("symbol determinant mismatch", m, r, theta, relative_error)
                    )
                eigenvalues, _ = mp.eigsy(matrix)
                observed_min = min(eigenvalues)
                observed_max = max(eigenvalues)
                if observed_min <= 0:
                    raise AssertionError(("symbol is not positive", m, r, theta, observed_min))
                if observed_min + mp.mpf("1e-45") < eigenvalue_floor:
                    raise AssertionError(
                        ("symbol floor failed", m, r, theta, observed_min, eigenvalue_floor)
                    )
                if observed_max > trace_bound + mp.mpf("1e-40"):
                    raise AssertionError(
                        ("symbol trace ceiling failed", m, r, theta, observed_max, trace_bound)
                    )
                symbol_rows.append(
                    {
                        "m": m,
                        "r": r,
                        "theta": theta,
                        "relative_det_error": mp.nstr(relative_error, 8),
                        "observed_min_eigenvalue": mp.nstr(observed_min, 16),
                        "explicit_floor": mp.nstr(eigenvalue_floor, 16),
                        "observed_max_eigenvalue": mp.nstr(observed_max, 16),
                        "trace_ceiling": mp.nstr(trace_bound, 16),
                        "determinant_floor": mp.nstr(determinant_floor, 16),
                    }
                )

            r_float = float(r)
            floor_float = float(eigenvalue_floor)
            ceiling_float = float(trace_bound)
            for J in section_lengths:
                gram = finite_gram(J, m, r_float)
                eigenvalues = np.linalg.eigvalsh(gram)
                observed_min = float(eigenvalues[0])
                observed_max = float(eigenvalues[-1])
                tolerance = 5e-10 * max(1.0, observed_max)
                if observed_min + tolerance < floor_float:
                    raise AssertionError(
                        ("finite section floor failed", J, m, r, observed_min, floor_float)
                    )
                if observed_max > ceiling_float + tolerance:
                    raise AssertionError(
                        ("finite section ceiling failed", J, m, r, observed_max, ceiling_float)
                    )
                section_rows.append(
                    {
                        "J": J,
                        "m": m,
                        "r": r,
                        "observed_min_eigenvalue": observed_min,
                        "explicit_floor": floor_float,
                        "observed_max_eigenvalue": observed_max,
                        "trace_ceiling": ceiling_float,
                    }
                )

    return {
        "symbol_cases": symbol_rows,
        "finite_section_cases": section_rows,
        "maximum_relative_symbol_determinant_error": mp.nstr(
            max_relative_det_error, 12
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-exact-m", type=int, default=5)
    parser.add_argument("--multiplicities", default="1,2,3,4")
    parser.add_argument("--ratios", default="0.05,0.15,0.4")
    parser.add_argument("--thetas", default="0,1.2,3.5,6.1")
    parser.add_argument("--section-lengths", default="1,2,5,10")
    parser.add_argument("--dps", type=int, default=70)
    parser.add_argument("--tail-tolerance", default="1e-60")
    parser.add_argument("--output")
    args = parser.parse_args()

    if args.max_exact_m < 1:
        raise SystemExit("--max-exact-m must be positive")
    mp.mp.dps = args.dps

    multiplicities = [int(value) for value in args.multiplicities.split(",")]
    ratios = [value.strip() for value in args.ratios.split(",")]
    thetas = [value.strip() for value in args.thetas.split(",")]
    section_lengths = [int(value) for value in args.section_lengths.split(",")]

    result = {
        "honesty": (
            "Finite symbolic and numerical replay only; the infinite theorem is "
            "proved in the accompanying note; this is not a zeta or RH proof."
        ),
        "exact_moment_checks": exact_moment_checks(args.max_exact_m),
        "numeric": run_numeric_cases(
            multiplicities,
            ratios,
            thetas,
            section_lengths,
            args.tail_tolerance,
        ),
        "parameters": {
            "max_exact_m": args.max_exact_m,
            "multiplicities": multiplicities,
            "ratios": ratios,
            "thetas": thetas,
            "section_lengths": section_lengths,
            "mpmath_dps": args.dps,
            "tail_tolerance": args.tail_tolerance,
        },
        "verified": True,
    }

    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(text)
    print(text, end="")


if __name__ == "__main__":
    main()
