"""Finite arithmetic and overlap-kernel routines for the log-Hardy check."""

from __future__ import annotations

import math
from collections.abc import Iterable

import numpy as np
from scipy.special import exp1


def primes_up_to(limit: int) -> np.ndarray:
    sieve = np.ones(limit + 1, dtype=np.bool_)
    sieve[:2] = False
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = False
    return np.flatnonzero(sieve)


def mangoldt_array(limit: int) -> np.ndarray:
    values = np.zeros(limit + 1, dtype=np.float64)
    for raw_prime in primes_up_to(limit):
        prime = int(raw_prime)
        log_prime = math.log(prime)
        power = prime
        while power <= limit:
            values[power] = log_prime
            if power > limit // prime:
                break
            power *= prime
    return values


def primitive(x: np.ndarray | float) -> np.ndarray | float:
    values = np.asarray(x, dtype=np.float64)
    logs = np.log(values)
    answer = exp1(logs) - 1.0 / (values * logs)
    return float(answer) if np.ndim(values) == 0 else answer


def interval_weight(left, right):
    return primitive(right) - primitive(left)


def ledger_rows(cutoffs: Iterable[int]) -> list[dict[str, float | int]]:
    ordered = sorted(set(int(value) for value in cutoffs))
    if not ordered or ordered[0] < 4:
        raise ValueError("cutoffs must be at least 4")
    centered = mangoldt_array(ordered[-1]) - 1.0
    centered[0] = 0.0
    prefix = np.cumsum(centered)
    rows = []
    for cutoff in ordered:
        cells = np.arange(2, cutoff, dtype=np.int64)
        moving = prefix[cells] - prefix[cells // 2]
        energy = float(np.dot(moving * moving, interval_weight(cells, cells + 1)))

        indices = np.arange(2, cutoff + 1, dtype=np.int64)
        upper = np.minimum(2 * indices, cutoff)
        active = upper > indices
        weights = np.zeros(indices.shape, dtype=np.float64)
        weights[active] = interval_weight(indices[active], upper[active])
        diagonal = float(np.dot(centered[2 : cutoff + 1] ** 2, weights))

        cross = energy - diagonal
        renormalizer = 0.5 * math.log(math.log(cutoff))
        rows.append({
            "cutoff": cutoff,
            "energy": energy,
            "diagonal": diagonal,
            "cross": cross,
            "half_log_log": renormalizer,
            "diagonal_error": diagonal - renormalizer,
            "renormalized_cross": cross + renormalizer,
        })
    return rows


def direct_gram_energy(cutoff: int, centered: np.ndarray) -> float:
    total = 0.0
    for m in range(2, cutoff + 1):
        for n in range(2, cutoff + 1):
            left = max(2, m, n)
            right = min(cutoff, 2 * m, 2 * n)
            if left < right:
                total += centered[m] * centered[n] * interval_weight(left, right)
    return float(total)


def exact_cell_energy(cutoff: int, centered: np.ndarray) -> float:
    prefix = np.cumsum(centered)
    total = 0.0
    for cell in range(2, cutoff):
        moving = prefix[cell] - prefix[cell // 2]
        total += moving * moving * interval_weight(cell, cell + 1)
    return float(total)
