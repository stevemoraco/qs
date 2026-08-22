#!/usr/bin/env python3
"""Exact certificate for the rank-20 Markman beta contraction map.

This script verifies only finite exterior-algebra identities over a rational
function field.  It does not formalize HKR, coherent sheaves, semiregularity,
or the Hodge conjecture.
"""

from __future__ import annotations

import json
from itertools import combinations
from typing import Dict, Iterable, Tuple

import sympy as sp

Monomial = Tuple[int, ...]
Form = Dict[Monomial, sp.Expr]


def wedge_monomial(left: Monomial, right: Monomial) -> tuple[int, Monomial]:
    if set(left).intersection(right):
        return 0, ()
    inversions = sum(1 for i in left for j in right if i > j)
    return (-1 if inversions % 2 else 1), tuple(sorted(left + right))


def wedge(left: Form, right: Form) -> Form:
    out: Form = {}
    for ml, cl in left.items():
        for mr, cr in right.items():
            sign, monomial = wedge_monomial(ml, mr)
            if sign:
                out[monomial] = sp.expand(out.get(monomial, 0) + sign * cl * cr)
    return {m: sp.expand(v) for m, v in out.items() if v != 0}


def power(form: Form, exponent: int) -> Form:
    out: Form = {(): sp.Integer(1)}
    for _ in range(exponent):
        out = wedge(out, form)
    return out


def contract_vector(index: int, form: Form) -> Form:
    out: Form = {}
    for monomial, coefficient in form.items():
        if index not in monomial:
            continue
        position = monomial.index(index)
        reduced = monomial[:position] + monomial[position + 1 :]
        out[reduced] = sp.expand(
            out.get(reduced, 0) + (-1) ** position * coefficient
        )
    return {m: sp.expand(v) for m, v in out.items() if v != 0}


def contract_bivector(first: int, second: int, form: Form) -> Form:
    return contract_vector(second, contract_vector(first, form))


def diagonal_11_form(weights: Iterable[sp.Expr]) -> Form:
    # x_i has index i, y_i has index 4+i.
    return {(i, 4 + i): sp.sympify(weight) for i, weight in enumerate(weights)}


def column(form: Form, target_basis: list[Monomial]) -> list[sp.Expr]:
    return [sp.expand(form.get(monomial, 0)) for monomial in target_basis]


def assert_zero_matrix(matrix: sp.Matrix) -> None:
    assert all(sp.simplify(entry) == 0 for entry in matrix), matrix


def main() -> None:
    a1, a2, b1, b2, c = sp.symbols("a1 a2 b1 b2 c", nonzero=True)
    delta = a1 * b2 - a2 * b1

    A = diagonal_11_form([a1, a1, a2, a2])
    B = diagonal_11_form([b1, b1, b2, b2])
    B3 = power(B, 3)

    y_pairs = list(combinations(range(4, 8), 2))
    x_pairs = list(combinations(range(4), 2))
    target_13 = sorted(
        tuple(sorted((x,) + ys))
        for x in range(4)
        for ys in combinations(range(4, 8), 3)
    )
    target_02 = y_pairs
    target_24 = [tuple(sorted(xs + tuple(range(4, 8)))) for xs in x_pairs]

    # Gerby/Poisson block: (xi, pi) |-> xi wedge A + c (pi contraction B^3).
    gp_columns: list[list[sp.Expr]] = []
    for pair in y_pairs:
        gp_columns.append(column(wedge({pair: sp.Integer(1)}, A), target_13))
    for pair in x_pairs:
        image = {
            monomial: sp.expand(c * coefficient)
            for monomial, coefficient in contract_bivector(*pair, B3).items()
        }
        gp_columns.append(column(image, target_13))
    gp_matrix = sp.Matrix(gp_columns).T

    # Commutative block: mu |-> (mu contraction A, c mu contraction B^3).
    ks_columns: list[list[sp.Expr]] = []
    for y_index in range(4):
        for vector_index in range(4):
            y_form = {(4 + y_index,): sp.Integer(1)}
            first = wedge(y_form, contract_vector(vector_index, A))
            second_raw = wedge(y_form, contract_vector(vector_index, B3))
            second = {
                monomial: sp.expand(c * coefficient)
                for monomial, coefficient in second_raw.items()
            }
            ks_columns.append(
                column(first, target_02) + column(second, target_24)
            )
    ks_matrix = sp.Matrix(ks_columns).T

    gp_rows = (0, 1, 2, 4, 5, 8, 10, 11, 14, 15)
    gp_cols = (0, 1, 2, 3, 4, 5, 7, 8, 9, 10)
    ks_rows = (0, 1, 2, 3, 4, 5, 7, 8, 9, 10)
    ks_cols = (1, 2, 3, 6, 7, 8, 9, 11, 12, 13)

    gp_det = sp.factor(gp_matrix.extract(gp_rows, gp_cols).det())
    ks_det = sp.factor(ks_matrix.extract(ks_rows, ks_cols).det())

    expected_gp_det = sp.factor(1296 * c**4 * a1 * a2 * b1**4 * b2**4 * delta**4)
    expected_ks_det = sp.factor(-expected_gp_det)
    assert sp.simplify(gp_det - expected_gp_det) == 0
    assert sp.simplify(ks_det - expected_ks_det) == 0

    # Two mixed gerby/Poisson kernel vectors.
    gp_kernel_vectors: list[sp.Matrix] = []
    vector = sp.zeros(12, 1)
    vector[0] = 6 * c * b1**2 * b2
    vector[6] = a2
    gp_kernel_vectors.append(vector)

    vector = sp.zeros(12, 1)
    vector[5] = 6 * c * b1 * b2**2
    vector[11] = a1
    gp_kernel_vectors.append(vector)

    for vector in gp_kernel_vectors:
        assert_zero_matrix(gp_matrix * vector)

    # Six block-diagonal symmetric Kodaira-Spencer kernel vectors.
    ks_kernel_vectors: list[sp.Matrix] = []
    for diagonal_column in (0, 5, 10, 15):
        vector = sp.zeros(16, 1)
        vector[diagonal_column] = 1
        ks_kernel_vectors.append(vector)

    vector = sp.zeros(16, 1)
    vector[1] = 1   # y_1 tensor e_2
    vector[4] = 1   # y_2 tensor e_1
    ks_kernel_vectors.append(vector)

    vector = sp.zeros(16, 1)
    vector[11] = 1  # y_3 tensor e_4
    vector[14] = 1  # y_4 tensor e_3
    ks_kernel_vectors.append(vector)

    for vector in ks_kernel_vectors:
        assert_zero_matrix(ks_matrix * vector)

    assert sp.Matrix.hstack(*gp_kernel_vectors).rank() == 2
    assert sp.Matrix.hstack(*ks_kernel_vectors).rank() == 6

    # Source-shaped rational specialization: embedding weights r^2=2 and r^-2=1/2.
    specialization = {
        a1: sp.Rational(2),
        a2: sp.Rational(1, 2),
        b1: sp.Rational(1, 2),
        b2: sp.Rational(2),
        c: sp.Rational(-1),
    }
    gp_rank = gp_matrix.subs(specialization).rank()
    ks_rank = ks_matrix.subs(specialization).rank()
    full_matrix = sp.diag(gp_matrix, ks_matrix)
    full_rank = full_matrix.subs(specialization).rank()

    assert gp_rank == 10
    assert ks_rank == 10
    assert full_rank == 20
    assert 28 - full_rank == 8

    receipt = {
        "status": "PASS",
        "scope": "finite exterior-algebra certificate only",
        "gerby_poisson_shape": list(gp_matrix.shape),
        "kodaira_spencer_shape": list(ks_matrix.shape),
        "gerby_poisson_minor": str(gp_det),
        "kodaira_spencer_minor": str(ks_det),
        "symbolic_kernel_vectors": {"gerby_poisson": 2, "kodaira_spencer": 6},
        "specialized_ranks": {
            "gerby_poisson": gp_rank,
            "kodaira_spencer": ks_rank,
            "total": full_rank,
            "total_nullity": 28 - full_rank,
        },
        "not_formalized": [
            "HKR",
            "Atiyah or obstruction maps",
            "coherent sheaves",
            "semiregularity",
            "Markman source object",
            "Hodge conjecture",
        ],
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
