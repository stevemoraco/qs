#!/usr/bin/env python3
"""Exact finite certificate for the proportional class Theta + c Theta^3.

The script verifies that the gerby/Poisson and Kodaira--Spencer contraction
blocks each have rank six, hence the total degree-two contraction rank is 12
and the total kernel dimension is 16.  It does not formalize derived-category
functoriality, semiregularity, or the Hodge conjecture.
"""

from __future__ import annotations

import json
from itertools import combinations
from typing import Dict, Tuple

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
    return {m: v for m, v in out.items() if v != 0}


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
    return {m: v for m, v in out.items() if v != 0}


def contract_bivector(first: int, second: int, form: Form) -> Form:
    return contract_vector(second, contract_vector(first, form))


def column(form: Form, target_basis: list[Monomial]) -> list[sp.Expr]:
    return [sp.expand(form.get(monomial, 0)) for monomial in target_basis]


def main() -> None:
    c = sp.symbols("c", nonzero=True)
    theta: Form = {(i, 4 + i): sp.Integer(1) for i in range(4)}
    theta3 = power(theta, 3)

    y_pairs = list(combinations(range(4, 8), 2))
    x_pairs = list(combinations(range(4), 2))
    target_13 = sorted(
        tuple(sorted((x,) + ys))
        for x in range(4)
        for ys in combinations(range(4, 8), 3)
    )
    target_02 = y_pairs
    target_24 = [tuple(sorted(xs + tuple(range(4, 8)))) for xs in x_pairs]

    gp_columns: list[list[sp.Expr]] = []
    for pair in y_pairs:
        gp_columns.append(column(wedge({pair: sp.Integer(1)}, theta), target_13))
    for pair in x_pairs:
        image = {
            monomial: sp.expand(c * coefficient)
            for monomial, coefficient in contract_bivector(*pair, theta3).items()
        }
        gp_columns.append(column(image, target_13))
    gp_matrix = sp.Matrix(gp_columns).T

    ks_columns: list[list[sp.Expr]] = []
    for y_index in range(4):
        for vector_index in range(4):
            y_form = {(4 + y_index,): sp.Integer(1)}
            first = wedge(y_form, contract_vector(vector_index, theta))
            second_raw = wedge(y_form, contract_vector(vector_index, theta3))
            second = {
                monomial: sp.expand(c * coefficient)
                for monomial, coefficient in second_raw.items()
            }
            ks_columns.append(column(first, target_02) + column(second, target_24))
    ks_matrix = sp.Matrix(ks_columns).T

    gp_minor_rows = (0, 1, 2, 4, 5, 8)
    gp_minor_cols = tuple(range(6))
    ks_minor_rows = tuple(range(6))
    ks_minor_cols = (1, 2, 3, 6, 7, 11)

    gp_minor = sp.factor(gp_matrix.extract(gp_minor_rows, gp_minor_cols).det())
    ks_minor = sp.factor(ks_matrix.extract(ks_minor_rows, ks_minor_cols).det())

    assert gp_minor == -1
    assert ks_minor == 1

    # The Poisson image is contained in the image of the gerby map.
    gerby = gp_matrix[:, :6]
    poisson = gp_matrix[:, 6:]
    assert gerby.rank() == 6
    assert gerby.row_join(poisson).rank() == 6

    # The degree-(2,4) Kodaira--Spencer output is determined by the degree-(0,2)
    # output, so the full block has the rank of its first six rows.
    assert ks_matrix[:6, :].rank() == 6
    assert ks_matrix.rank() == 6

    total_rank = sp.diag(gp_matrix, ks_matrix).rank()
    assert total_rank == 12
    assert 28 - total_rank == 16

    receipt = {
        "status": "PASS",
        "scope": "finite proportional exterior-algebra certificate only",
        "gerby_poisson_shape": list(gp_matrix.shape),
        "kodaira_spencer_shape": list(ks_matrix.shape),
        "gerby_poisson_rank": gp_matrix.rank(),
        "kodaira_spencer_rank": ks_matrix.rank(),
        "total_rank": total_rank,
        "total_nullity": 28 - total_rank,
        "selected_minors": {
            "gerby_poisson": str(gp_minor),
            "kodaira_spencer": str(ks_minor),
        },
        "not_formalized": [
            "HKR",
            "Fourier-Mukai functoriality",
            "semiregularity",
            "Markman source sheaves",
            "Hodge conjecture",
        ],
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
