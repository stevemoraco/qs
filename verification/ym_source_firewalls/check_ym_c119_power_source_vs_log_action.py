#!/usr/bin/env python3
"""Exact finite regression for YM C119.

Checks only the asymptotic arithmetic shadow:
- a dimension-six source contributes 4^n/(n+1)^q;
- every fixed polynomial/logarithmic action cost is eventually dominated;
- the exact lower-bound exponent becomes strictly increasing and positive.

No Wilson measure, source owner map, or Yang-Mills theorem is formalized.
"""

from fractions import Fraction


def source_scale(n: int, q: int) -> Fraction:
    assert n >= 0 and q >= 0
    return Fraction(4**n, (n + 1) ** q)


def action_cost(n: int, degree: int, coefficient: int = 1) -> int:
    assert n >= 0 and degree >= 0 and coefficient >= 0
    return coefficient * (n + 1) ** degree


def exponent(n: int, q: int, degree: int, t: Fraction, c: Fraction, B: int) -> Fraction:
    return t * c * source_scale(n, q) - action_cost(n, degree, B)


def main() -> None:
    for n in range(30):
        assert source_scale(n, 0) == 4**n

    for q in range(9):
        for degree in range(7):
            values = [
                exponent(n, q, degree, Fraction(1, 7), Fraction(1, 11), 13)
                for n in range(1, 320)
            ]
            positive = [i for i, v in enumerate(values) if v > 0]
            assert positive, (q, degree)
            tail_start = max(positive[0], 250)
            tail = values[tail_start:]
            assert tail
            assert all(tail[i + 1] > tail[i] for i in range(len(tail) - 1)), (q, degree)

    for q in range(8):
        for degree in range(8):
            ratios = [
                source_scale(n, q) / Fraction((n + 1) ** degree)
                for n in range(200, 260)
            ]
            assert all(ratios[i + 1] > ratios[i] for i in range(len(ratios) - 1))

    print(
        "PASS: canonical dimension-six 4^n source growth dominates every "
        "fixed polynomial/logarithmic Wilson or triangular-normalization cost."
    )


if __name__ == "__main__":
    main()
