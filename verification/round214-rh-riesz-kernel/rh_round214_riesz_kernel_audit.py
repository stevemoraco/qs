#!/usr/bin/env python3
"""Exact finite checks for Round 214's RH support-hole kernel.

This script is a discovery/falsification aid. It verifies selected rational
identities using only Fraction and scans a finite rational grid. It does not
prove any continuum statement and it does not prove RH.
"""

from fractions import Fraction
from math import comb


def positive_part(x: Fraction) -> Fraction:
    return x if x > 0 else Fraction(0)


def mu_squared(a: Fraction) -> Fraction:
    return Fraction(210) * (a * a + 16) / (a * a * (151 * a * a + 840))


def h_kernel(a: Fraction, t: Fraction) -> Fraction:
    r = t / a
    mu2 = mu_squared(a)
    total = Fraction(0)
    for k in range(9):
        y = positive_part(r + 4 - k)
        bracket = (
            y**3 / (6 * a)
            + a * (mu2 - Fraction(1, 4)) * y**5 / 120
            - mu2 * a**3 * y**7 / 20160
        )
        total += (-1) ** k * comb(8, k) * bracket
    return total


def d_polynomial(a: Fraction) -> Fraction:
    return a * a * (840 + 151 * a * a)


def normalized_kernel(a: Fraction, t: Fraction) -> Fraction:
    return a**4 * d_polynomial(a) * h_kernel(a, t) / 16


def p1_shifted(x: Fraction) -> Fraction:
    return (
        3152 * x**7 + 22064 * x**6 + 181812 * x**5 +
        604917 * x**4 + 1317648 * x**3 + 1406429 * x**2 +
        747402 * x + 123084
    )


def p2_shifted(x: Fraction) -> Fraction:
    return (
        273 * x**9 - 308 * x**8 - 20017 * x**7 - 7273 * x**6 +
        35723 * x**5 + 599042 * x**4 + 540413 * x**3 +
        231307 * x**2 - 18792 * x - 9648
    )


def w_at_one_polynomial(a: Fraction) -> Fraction:
    return -p1_shifted(a - 1) / 1536


def w_at_two_polynomial(a: Fraction) -> Fraction:
    return -p2_shifted(a - 1) / 240


def p2_crude_upper_bound() -> Fraction:
    eighth = Fraction(1, 8)
    return (
        273 * eighth**9 + 35723 * eighth**5 + 599042 * eighth**4 +
        540413 * eighth**3 + 231307 * eighth**2 - 9648
    )


def exact_certificates() -> None:
    one = Fraction(1)
    two = Fraction(2)
    assert mu_squared(one) == Fraction(3570, 991)
    assert h_kernel(one, one) == Fraction(-10257, 7928)
    assert h_kernel(one, two) == Fraction(3216, 4955)
    assert normalized_kernel(one, one) == Fraction(-10257, 128)
    assert normalized_kernel(one, two) == Fraction(201, 5)
    assert p2_crude_upper_bound() == Fraction(-648404946671, 134217728)
    assert p2_crude_upper_bound() < 0

    for j in range(126):
        a = Fraction(1000 + j, 1000)
        assert normalized_kernel(a, one) == w_at_one_polynomial(a)
        assert normalized_kernel(a, two) == w_at_two_polynomial(a)
        if a <= Fraction(9, 8):
            assert normalized_kernel(a, one) < 0
            assert normalized_kernel(a, two) > 0


def main() -> None:
    exact_certificates()
    print("ROUND214 EXACT FINITE CHECKS: PASS")
    print("w_1(1) =", normalized_kernel(Fraction(1), Fraction(1)))
    print("w_1(2) =", normalized_kernel(Fraction(1), Fraction(2)))
    print("P2 crude upper bound =", p2_crude_upper_bound())
    print("HONESTY: finite checks only; no continuum or RH conclusion.")


if __name__ == "__main__":
    main()
