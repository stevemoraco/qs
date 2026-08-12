#!/usr/bin/env python3
"""Exact-rational certificate for the two four-dimensional blocks in
Markman's genus-4 contraction kernel.

This verifies only finite exterior-algebra identities. It does not compute the
object obstruction map and does not prove semiregularity or the Hodge conjecture.
"""
from fractions import Fraction
from itertools import combinations

NGEN = 8  # x0..x3,y0..y3


def wedge_monom(mask1, mask2):
    if mask1 & mask2:
        return None, 0
    e1 = [i for i in range(NGEN) if (mask1 >> i) & 1]
    e2 = [i for i in range(NGEN) if (mask2 >> i) & 1]
    inversions = sum(1 for i in e1 for j in e2 if j < i)
    return mask1 | mask2, -1 if inversions % 2 else 1


def add(a, b, scale=Fraction(1)):
    out = dict(a)
    for monomial, coefficient in b.items():
        out[monomial] = out.get(monomial, Fraction(0)) + scale * coefficient
        if out[monomial] == 0:
            del out[monomial]
    return out


def wedge(a, b):
    out = {}
    for mask1, coefficient1 in a.items():
        for mask2, coefficient2 in b.items():
            mask, sign = wedge_monom(mask1, mask2)
            if mask is not None:
                out[mask] = out.get(mask, Fraction(0)) + (
                    coefficient1 * coefficient2 * sign
                )
    return {mask: coefficient for mask, coefficient in out.items() if coefficient}


def basis(index):
    return {1 << index: Fraction(1)}


def contract(form, index):
    out = {}
    for mask, coefficient in form.items():
        if not ((mask >> index) & 1):
            continue
        position = sum(1 for j in range(index) if (mask >> j) & 1)
        new_mask = mask & ~(1 << index)
        out[new_mask] = out.get(new_mask, Fraction(0)) + (
            coefficient * ((-1) ** position)
        )
    return {mask: coefficient for mask, coefficient in out.items() if coefficient}


def power(form, exponent):
    out = {0: Fraction(1)}
    for _ in range(exponent):
        out = wedge(out, form)
    return out


def diagonal_form(coefficients):
    out = {}
    for i, coefficient in enumerate(coefficients):
        out = add(
            out,
            wedge(basis(i), basis(4 + i)),
            Fraction(coefficient),
        )
    return out


def beta_form(a, b, q):
    return add(
        diagonal_form(a),
        power(diagonal_form(b), 3),
        -Fraction(q, 6),
    )


def action_matrix(a, b, q):
    beta = beta_form(a, b, q)
    columns = []
    labels = []

    for i, j in combinations(range(4), 2):
        alpha = wedge(basis(4 + i), basis(4 + j))
        columns.append(wedge(alpha, beta))
        labels.append(("alpha", i, j))

    for i in range(4):
        for j in range(4):
            columns.append(wedge(basis(4 + j), contract(beta, i)))
            labels.append(("B", i, j))

    for i, j in combinations(range(4), 2):
        columns.append(contract(contract(beta, i), j))
        labels.append(("gamma", i, j))

    output_basis = sorted(set().union(*(column.keys() for column in columns)))
    matrix = [
        [column.get(mask, Fraction(0)) for column in columns]
        for mask in output_basis
    ]
    return matrix, labels


def rref_nullspace(matrix):
    a = [row[:] for row in matrix]
    rows = len(a)
    columns = len(a[0])
    pivots = []
    row = 0

    for column in range(columns):
        pivot = next(
            (i for i in range(row, rows) if a[i][column] != 0),
            None,
        )
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        pivot_value = a[row][column]
        a[row] = [entry / pivot_value for entry in a[row]]
        for i in range(rows):
            if i != row and a[i][column] != 0:
                factor = a[i][column]
                a[i] = [
                    x - factor * y
                    for x, y in zip(a[i], a[row])
                ]
        pivots.append(column)
        row += 1
        if row == rows:
            break

    free = [column for column in range(columns) if column not in pivots]
    basis_vectors = []
    for free_column in free:
        vector = [Fraction(0)] * columns
        vector[free_column] = Fraction(1)
        for i, pivot_column in enumerate(pivots):
            vector[pivot_column] = -a[i][free_column]
        basis_vectors.append(vector)

    return len(pivots), basis_vectors


def sparse_vector(labels, vector):
    return {
        label: coefficient
        for label, coefficient in zip(labels, vector)
        if coefficient
    }


def expected_basis(q):
    return [
        {("B", 0, 0): Fraction(1)},
        {("B", 0, 1): Fraction(1), ("B", 1, 0): Fraction(1)},
        {("B", 1, 1): Fraction(1)},
        {("B", 2, 2): Fraction(1)},
        {("B", 2, 3): Fraction(1), ("B", 3, 2): Fraction(1)},
        {("B", 3, 3): Fraction(1)},
        {("alpha", 0, 1): Fraction(-q), ("gamma", 0, 1): Fraction(1)},
        {("alpha", 2, 3): Fraction(-q), ("gamma", 2, 3): Fraction(1)},
    ]


def check_case(u, q):
    u = Fraction(u)
    a = (u * u, u * u, 1 / (u * u), 1 / (u * u))
    b = (1 / (u * u), 1 / (u * u), u * u, u * u)

    matrix, labels = action_matrix(a, b, q)
    rank, nullspace = rref_nullspace(matrix)
    sparse = [sparse_vector(labels, vector) for vector in nullspace]

    assert rank == 20, (u, q, rank)
    assert len(nullspace) == 8, (u, q, len(nullspace))
    assert sparse == expected_basis(q), (u, q, sparse)

    print(
        f"u={u}, q={q}: rank=20, kernel=8; "
        "generalized vectors gamma_01-q alpha_01 and gamma_23-q alpha_23"
    )


def main():
    cases = [
        (Fraction(2), 1),
        (Fraction(2), 3),
        (Fraction(3, 2), 2),
        (Fraction(5, 3), 7),
    ]
    for u, q in cases:
        check_case(u, q)
    print("EXACT CERTIFICATE: PASS")
    print(
        "KERNEL BLOCKS: Sym2(U1*) + <gamma1-q alpha1>, "
        "Sym2(U2*) + <gamma2-q alpha2>"
    )


if __name__ == "__main__":
    main()
