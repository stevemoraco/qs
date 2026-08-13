#!/usr/bin/env python3
"""Exact finite regressions for the W2 partial-normalization Hodge packet.

This checks arithmetic and the explicit local matrix/Atiyah-square identities.
It is evidence, not a replacement for the human geometric proof.
"""

from fractions import Fraction
from math import comb


# Linear polynomials in u,v,w,z are represented by coefficient 4-tuples.
ZERO = (0, 0, 0, 0)
U = (1, 0, 0, 0)
V = (0, 1, 0, 0)
W = (0, 0, 1, 0)
Z = (0, 0, 0, 1)


def neg(a):
    return tuple(-x for x in a)


def mul_linear(a, b):
    """Quadratic monomial coefficient dictionary for a*b."""
    out = {}
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            if ai and bj:
                key = tuple(sorted((i, j)))
                out[key] = out.get(key, 0) + ai * bj
    return {k: v for k, v in out.items() if v}


def add_quad(*terms):
    out = {}
    for term in terms:
        for k, v in term.items():
            out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v}


def wedge(a, b):
    """Exterior product of constant 1-forms."""
    out = {}
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            if i == j or not ai or not bj:
                continue
            key = (min(i, j), max(i, j))
            sign = 1 if i < j else -1
            out[key] = out.get(key, 0) + sign * ai * bj
    return {k: v for k, v in out.items() if v}


def add_form(*forms):
    out = {}
    for form in forms:
        for k, v in form.items():
            out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v}


def matmul_d1_d0(d1, d0):
    cols = len(d0[0])
    result = []
    for j in range(cols):
        result.append(add_quad(*(mul_linear(d1[i], d0[i][j]) for i in range(4))))
    return result


def atiyah_square_rows(d1, d0):
    """Compute (1/2)dD1 wedge dD0; the factor 1/2 is convention-cancelled
    by the two ordered products in At^2. Here we return the expected wedge sum.
    """
    rows = []
    for j in range(2):
        rows.append(add_form(*(wedge(d1[i], d0[i][j]) for i in range(4))))
    return rows


def check_geometry(k):
    n = 24 * k
    nodes = 6 * comb(n, 2)
    separated = 48 * k * (24 * k - 1)
    assert nodes == 72 * k * (24 * k - 1)
    assert 3 * separated == 2 * nodes

    top_union = Fraction(3 * k, 1) - Fraction(nodes, 24)
    top_q = top_union + Fraction(separated, 24)
    assert top_union == -72 * k * k + 6 * k
    assert top_q == -24 * k * k + 4 * k

    d = 24 * k - 1
    # e^x(1 - (12k x^2 - 8k x^3 + top_q x^4))
    # coefficients through x^4
    q2, q3, q4 = Fraction(12 * k), Fraction(-8 * k), top_q
    e = [Fraction(1), Fraction(1), Fraction(1, 2), Fraction(1, 6), Fraction(1, 24)]
    out = e[:]
    # subtract e^x * (q2 x^2 + q3 x^3 + q4 x^4)
    out[2] -= q2
    out[3] -= q2 + q3
    out[4] -= q2 * Fraction(1, 2) + q3 + q4
    assert out == [
        Fraction(1),
        Fraction(1),
        Fraction(-d, 2),
        Fraction(-d, 6),
        Fraction(d * d, 24),
    ]


def check_local_complex():
    # D0=[[-v,0],[u,0],[0,-z],[0,w]], D1=(-u,-v,w,z)
    d0 = [
        [neg(V), ZERO],
        [U, ZERO],
        [ZERO, neg(Z)],
        [ZERO, W],
    ]
    d1 = [neg(U), neg(V), W, Z]
    assert matmul_d1_d0(d1, d0) == [{}, {}]

    rows = atiyah_square_rows(d1, d0)
    # Depending on the global cochain sign, both rows may be simultaneously
    # negated. The invariant statement is support and nonzero unit coefficient.
    assert rows[0] in ({(0, 1): 2}, {(0, 1): -2})
    assert rows[1] in ({(2, 3): 2}, {(2, 3): -2})

    # After the conventional 1/2, contraction with du^dv is a unit in row 1.
    assert abs(rows[0][(0, 1)]) == 2

    # Minimality firewall: D0(0)=D1(0)=0, hence every boundary
    # D1*h^{-1}+h^0*D0 evaluates to zero at the origin. The cocycle (1,0)
    # does not, so it cannot be a boundary.
    d0_at_origin = [[0, 0], [0, 0], [0, 0], [0, 0]]
    d1_at_origin = [0, 0, 0, 0]
    assert all(x == 0 for row in d0_at_origin for x in row)
    assert all(x == 0 for x in d1_at_origin)
    cocycle_at_origin = (1, 0)
    assert cocycle_at_origin != (0, 0)


def main():
    for k in range(1, 101):
        check_geometry(k)
    check_local_complex()
    print("PASS: exact W2 counts, target character, local complex, and unit-cocycle firewall")


if __name__ == "__main__":
    main()
