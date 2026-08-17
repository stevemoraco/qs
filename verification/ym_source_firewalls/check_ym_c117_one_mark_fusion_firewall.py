#!/usr/bin/env python3
"""Dependency-free exact regression for YM C117.

This checks only finite arithmetic shadows:
- fixed-order derivative values for W_M(z)=sum n! z^n;
- invisibility of the high-order tail to any fixed D-jet;
- growth at every positive rational radius;
- the sharp equality model for the sufficient one-mark fusion recurrence.

It does not verify Kirk v4, RG estimates, source renormalization, OS axioms,
or the Yang-Mills mass gap.
"""

from fractions import Fraction
from math import factorial


def derivative_at_zero(M: int, n: int) -> int:
    return 0 if n > M else factorial(n) ** 2


def hidden_tail_derivative_at_zero(M: int, D: int, n: int) -> int:
    if n <= D or n > M:
        return 0
    return factorial(n) ** 2


def term(n: int, r: Fraction) -> Fraction:
    return Fraction(factorial(n)) * r**n


def equality_fusion_sequence(N: int, K: int, C1: int) -> list[int]:
    assert N >= 1 and K >= 0 and C1 > 0
    values = [1, C1]
    for n in range(1, N):
        values.append(K * (n + 1) * C1 * values[n])
    return values


def main() -> None:
    for n in range(10):
        expected = factorial(n) ** 2
        for M in range(n, 25):
            assert derivative_at_zero(M, n) == expected

    for D in range(9):
        for M in range(D + 1, D + 15):
            for n in range(D + 1):
                assert hidden_tail_derivative_at_zero(M, D, n) == 0
            assert hidden_tail_derivative_at_zero(M, D, M) == factorial(M) ** 2

    for q in range(1, 16):
        r = Fraction(1, q)
        for n in range(q, q + 15):
            assert term(n + 1, r) / term(n, r) == Fraction(n + 1, q)
            assert term(n + 1, r) > term(n, r)

    for K in range(1, 6):
        for C1 in range(1, 6):
            values = equality_fusion_sequence(12, K, C1)
            for n in range(1, 13):
                assert values[n] == factorial(n) * K ** (n - 1) * C1**n

    print(
        "PASS: fixed-order and finite-jet control coexist with zero common "
        "radius; the one-mark fusion recurrence yields the claimed factorial bound."
    )


if __name__ == "__main__":
    main()
