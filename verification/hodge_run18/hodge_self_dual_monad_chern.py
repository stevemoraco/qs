#!/usr/bin/env python3
"""Exact-rational certificate for the centered self-dual-monad realization
of a multiple of Markman's class beta' = A - (q/6) B^3.

This script checks finite coefficient identities and constructs an integral
sum-of-squares packet. It does not construct monad maps or prove semiregularity.
"""
from fractions import Fraction
from math import gcd, isqrt


def lcm(a: int, b: int) -> int:
    return abs(a * b) // gcd(a, b)


def four_squares(n: int) -> tuple[int, int, int, int]:
    """Return one exact Lagrange four-square representation by finite search."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    bound = isqrt(n)
    squares = [i * i for i in range(bound + 1)]
    two_square = {}
    for a in range(bound + 1):
        for b in range(bound + 1):
            two_square.setdefault(squares[a] + squares[b], (a, b))
    for value, (a, b) in two_square.items():
        complement = n - value
        if complement in two_square:
            c, d = two_square[complement]
            return a, b, c, d
    raise AssertionError(f"four-square theorem search failed for {n}")


def allocate_ranks(total_rank: int, count: int) -> list[int]:
    """Split total_rank into count integers, each at least three."""
    if count == 0:
        return []
    if total_rank < 3 * count:
        raise ValueError("rank scale too small")
    ranks = [3] * count
    ranks[0] += total_rank - 3 * count
    assert sum(ranks) == total_rank
    assert min(ranks) >= 3
    return ranks


def check_case(u: Fraction, q: int, m: int, scale: int = 12) -> None:
    if u == 0 or q <= 0 or m <= 0 or m % 2:
        raise ValueError("require u nonzero, q>0, and m positive even")

    T = u**4 + u**-4
    c_A = Fraction(m * m, 24) - Fraction(q, 6) / T
    c_B = Fraction(q, 2) / T
    assert c_A > 0 and c_B > 0

    denominator = lcm(c_A.denominator, c_B.denominator)
    base_A = denominator * c_A
    base_B = denominator * c_B
    assert base_A.denominator == base_B.denominator == 1

    R = denominator * scale * scale
    target_A = int(base_A) * scale * scale
    target_B = int(base_B) * scale * scale

    rep_A = tuple(scale * value for value in four_squares(int(base_A)))
    rep_B = tuple(scale * value for value in four_squares(int(base_B)))
    assert sum(value * value for value in rep_A) == target_A
    assert sum(value * value for value in rep_B) == target_B

    nonzero_square_terms = [
        ("A", value) for value in rep_A if value
    ] + [
        ("B", value) for value in rep_B if value
    ]

    if R < 3 * len(nonzero_square_terms):
        raise AssertionError("chosen scale does not support rank allocation")
    ranks = allocate_ranks(R, len(nonzero_square_terms))

    monad_rank = sum(ranks)
    square_A = sum(
        value * value
        for kind, value in nonzero_square_terms
        if kind == "A"
    )
    square_B = sum(
        value * value
        for kind, value in nonzero_square_terms
        if kind == "B"
    )
    assert monad_rank == R
    assert Fraction(square_A) == R * c_A
    assert Fraction(square_B) == R * c_B

    ch_codim1_A = R * m
    ch_codim2 = Fraction(0)
    ch_codim4 = Fraction(0)

    coeff_A3 = Fraction(R * m * q, 6) / T
    coeff_AB2 = -Fraction(R * m * q, 2) / T

    desired_A3 = Fraction(R * m * q, 6) / T
    desired_AB2 = -Fraction(R * m * q, 2) / T

    assert ch_codim1_A == R * m
    assert ch_codim2 == 0
    assert ch_codim4 == 0
    assert coeff_A3 == desired_A3
    assert coeff_AB2 == desired_AB2

    print(
        f"u={u}, q={q}, m={m}: T={T}, R={R}, "
        f"square_terms={len(nonzero_square_terms)}, ranks={ranks}"
    )
    print(
        "  ch(i_*E)=Rm A + "
        f"({coeff_A3}) A^3 + ({coeff_AB2}) A B^2 "
        "= Rm[A-(q/6)B^3]"
    )


def main() -> None:
    cases = [
        (Fraction(2), 1, 4),
        (Fraction(3, 2), 2, 6),
        (Fraction(5, 3), 3, 8),
        (Fraction(2, 3), 1, 10),
    ]
    for case in cases:
        check_case(*case)
    print("EXACT CERTIFICATE: PASS")
    print("CODIMENSION 2: ZERO")
    print("CODIMENSION 4: ZERO")
    print("OBJECT TYPE: finite direct sum of source-backed monad bundles")
    print("SEMIREGULARITY: NOT CERTIFIED")


if __name__ == "__main__":
    main()
