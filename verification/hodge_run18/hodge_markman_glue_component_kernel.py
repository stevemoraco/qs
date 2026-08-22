#!/usr/bin/env python3
"""Exact-rational certificate for the component-kernel intersection in
Markman's glued genus-4 sheaf construction.

It verifies only finite exterior-algebra contraction identities.
"""
from fractions import Fraction
from itertools import combinations

from hodge_markman_kernel_block_basis import (
    add,
    basis,
    contract,
    diagonal_form,
    power,
    rref_nullspace,
    sparse_vector,
    wedge,
)


def action_matrix_for_form(beta):
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


def ordinary_rm_basis():
    return [
        {("B", 0, 0): Fraction(1)},
        {("B", 0, 1): Fraction(1), ("B", 1, 0): Fraction(1)},
        {("B", 1, 1): Fraction(1)},
        {("B", 2, 2): Fraction(1)},
        {("B", 2, 3): Fraction(1), ("B", 3, 2): Fraction(1)},
        {("B", 3, 3): Fraction(1)},
    ]


def total_basis(q):
    return ordinary_rm_basis() + [
        {("alpha", 0, 1): Fraction(-q), ("gamma", 0, 1): Fraction(1)},
        {("alpha", 2, 3): Fraction(-q), ("gamma", 2, 3): Fraction(1)},
    ]


def nullspace(matrix):
    rank, vectors = rref_nullspace(matrix)
    return rank, vectors


def check_case(u, q, d):
    u = Fraction(u)
    assert u != 0
    assert d > q * max(u**4, u**-4)

    a_coefficients = (u * u, u * u, 1 / (u * u), 1 / (u * u))
    b_coefficients = (1 / (u * u), 1 / (u * u), u * u, u * u)

    a_form = diagonal_form(a_coefficients)
    b_form = diagonal_form(b_coefficients)

    secant = add(a_form, power(a_form, 3), -Fraction(d, 6))
    curve = add({}, power(a_form, 3), Fraction(d, 6))
    curve = add(curve, power(b_form, 3), -Fraction(q, 6))
    total = add(secant, curve)

    secant_matrix, labels = action_matrix_for_form(secant)
    curve_matrix, curve_labels = action_matrix_for_form(curve)
    total_matrix, total_labels = action_matrix_for_form(total)
    assert labels == curve_labels == total_labels

    secant_rank, secant_null = nullspace(secant_matrix)
    curve_rank, curve_null = nullspace(curve_matrix)
    total_rank, total_null = nullspace(total_matrix)
    intersection_rank, intersection_null = nullspace(secant_matrix + curve_matrix)

    assert secant_rank == 12 and len(secant_null) == 16
    assert curve_rank == 12 and len(curve_null) == 16
    assert intersection_rank == 22 and len(intersection_null) == 6
    assert total_rank == 20 and len(total_null) == 8

    sparse_intersection = [
        sparse_vector(labels, vector) for vector in intersection_null
    ]
    sparse_total = [sparse_vector(labels, vector) for vector in total_null]

    assert sparse_intersection == ordinary_rm_basis()
    assert sparse_total == total_basis(q)

    print(
        f"u={u}, q={q}, d={d}: "
        "ker(secant)=16, ker(curve)=16, intersection=6, total=8"
    )


def main():
    cases = [
        (Fraction(2), 1, 17),
        (Fraction(3, 2), 2, 11),
        (Fraction(5, 3), 1, 8),
        (Fraction(2, 3), 3, 16),
    ]
    for case in cases:
        check_case(*case)
    print("EXACT CERTIFICATE: PASS")
    print("COMMON KERNEL: exactly the six ordinary RM directions")
    print("TOTAL-ONLY DIRECTIONS: gamma_i-q alpha_i for i=1,2")


if __name__ == "__main__":
    main()
