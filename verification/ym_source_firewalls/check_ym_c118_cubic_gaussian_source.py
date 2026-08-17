#!/usr/bin/env python3
"""Exact arithmetic regression for YM C118.

Checks:
- exact Gaussian cubic even-moment coefficients;
- the coefficient ratio and a linear lower bound tending to infinity;
- the exact quartic-stabilized exponent at x=t/(2u).

This does not verify a Yang-Mills source normalization or any QFT theorem.
"""

from fractions import Fraction
from math import factorial


def cubic_even_coefficient(n: int) -> Fraction:
    assert n >= 0
    return Fraction(factorial(6 * n), 2 ** (3 * n) * factorial(3 * n) * factorial(2 * n))


def exact_ratio(n: int) -> Fraction:
    assert n >= 0
    return cubic_even_coefficient(n + 1) / cubic_even_coefficient(n)


def product_ratio(n: int) -> Fraction:
    assert n >= 0
    num = 1
    for j in range(1, 7):
        num *= 6 * n + j
    den = 8
    for j in range(1, 4):
        den *= 3 * n + j
    den *= (2 * n + 1) * (2 * n + 2)
    return Fraction(num, den)


def stabilized_exponent(u: Fraction, t: Fraction) -> Fraction:
    assert u > 0
    x = t / (2 * u)
    return -x * x / 2 - u * x**4 + t * x**3


def closed_stabilized_exponent(u: Fraction, t: Fraction) -> Fraction:
    return t * t * (t * t - 2 * u) / (16 * u**3)


def main() -> None:
    for n in range(0, 30):
        assert exact_ratio(n) == product_ratio(n)

    for n in range(1, 200):
        assert exact_ratio(n) >= Fraction(27 * n, 16)

    for t in [Fraction(1, 1), Fraction(2, 3), Fraction(5, 4)]:
        values = []
        qs = [4, 8, 16, 32, 64, 128]
        for q in qs:
            u = Fraction(1, q)
            lhs = stabilized_exponent(u, t)
            rhs = closed_stabilized_exponent(u, t)
            assert lhs == rhs
            values.append(lhs)
        tail = [v for q, v in zip(qs, values) if Fraction(1, q) < t * t / 2]
        assert all(tail[i + 1] > tail[i] for i in range(len(tail) - 1))

    print(
        "PASS: cubic Gaussian source coefficients have zero radius; "
        "quartic stabilization loses every fixed source bound as u->0."
    )


if __name__ == "__main__":
    main()
