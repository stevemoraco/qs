#!/usr/bin/env python3
"""Exact-rational certificate for the separated centered-monad direct-sum
common-kernel obstruction.

The script verifies finite contraction matrices only. The object-level
conclusion additionally uses Huang's kernel inclusion, as documented in the
companion note.
"""
from fractions import Fraction

from hodge_markman_kernel_block_basis import (
    add,
    diagonal_form,
    expected_basis,
    power,
    rref_nullspace,
    sparse_vector,
    wedge,
)
from hodge_markman_glue_component_kernel import action_matrix_for_form
from hodge_self_dual_monad_chern import allocate_ranks, four_squares, lcm


def ordinary_rm_basis():
    return expected_basis(0)[:6]


def build_packet(u, q, m, scale=12):
    T = u**4 + u**-4
    c_A = Fraction(m * m, 24) - Fraction(q, 6) / T
    c_B = Fraction(q, 2) / T
    assert c_A > 0 and c_B > 0

    denominator = lcm(c_A.denominator, c_B.denominator)
    base_A = denominator * c_A
    base_B = denominator * c_B
    assert base_A.denominator == base_B.denominator == 1

    R = denominator * scale * scale
    rep_A = tuple(scale * value for value in four_squares(int(base_A)))
    rep_B = tuple(scale * value for value in four_squares(int(base_B)))

    terms = [("A", value) for value in rep_A if value]
    terms += [("B", value) for value in rep_B if value]
    ranks = allocate_ranks(R, len(terms))

    assert sum(ranks) == R
    assert sum(value * value for kind, value in terms if kind == "A") == R * c_A
    assert sum(value * value for kind, value in terms if kind == "B") == R * c_B

    a_terms = [
        (value, rank)
        for (kind, value), rank in zip(terms, ranks)
        if kind == "A"
    ]
    b_terms = [
        (value, rank)
        for (kind, value), rank in zip(terms, ranks)
        if kind == "B"
    ]
    assert len(a_terms) >= 2 and len(b_terms) >= 1
    assert len({Fraction(value * value, rank) for value, rank in a_terms}) >= 2

    return R, terms, ranks


def component_class(A, B, kind, coefficient, rank, m):
    beta = add({}, A, Fraction(rank))
    beta = add(beta, power(A, 3), Fraction(rank * m * m, 24))
    H = A if kind == "A" else B
    beta = add(beta, wedge(A, wedge(H, H)), -Fraction(coefficient * coefficient))
    return beta


def check_case(u, q, m):
    u = Fraction(u)
    R, terms, ranks = build_packet(u, q, m)

    a_coefficients = (u * u, u * u, 1 / (u * u), 1 / (u * u))
    b_coefficients = (1 / (u * u), 1 / (u * u), u * u, u * u)
    A = diagonal_form(a_coefficients)
    B = diagonal_form(b_coefficients)

    stacked_matrix = []
    total_class = {}
    labels = None

    for (kind, coefficient), rank in zip(terms, ranks):
        beta = component_class(A, B, kind, coefficient, rank, m)
        matrix, current_labels = action_matrix_for_form(beta)
        if labels is None:
            labels = current_labels
        else:
            assert current_labels == labels
        stacked_matrix.extend(matrix)
        total_class = add(total_class, beta)

    common_rank, common_nullspace = rref_nullspace(stacked_matrix)
    total_matrix, total_labels = action_matrix_for_form(total_class)
    total_rank, total_nullspace = rref_nullspace(total_matrix)
    assert total_labels == labels

    sparse_common = [
        sparse_vector(labels, vector) for vector in common_nullspace
    ]
    sparse_total = [
        sparse_vector(labels, vector) for vector in total_nullspace
    ]

    assert common_rank == 22
    assert len(common_nullspace) == 6
    assert sparse_common == ordinary_rm_basis()

    assert total_rank == 20
    assert len(total_nullspace) == 8
    assert sparse_total == expected_basis(q)

    generalized = expected_basis(q)[6:]
    assert all(vector not in sparse_common for vector in generalized)

    print(
        f"u={u}, q={q}, m={m}, R={R}: "
        "component-common rank=22/kernel=6; total rank=20/kernel=8"
    )


def main():
    cases = [
        (Fraction(2), 1, 4),
        (Fraction(3, 2), 2, 6),
        (Fraction(5, 3), 3, 8),
        (Fraction(2, 3), 1, 10),
    ]
    for case in cases:
        check_case(*case)
    print("EXACT CERTIFICATE: PASS")
    print("COMMON COMPONENT KERNEL: six ordinary RM directions")
    print("TOTAL KERNEL: six ordinary plus gamma_i-q alpha_i")
    print("DIRECT-SUM PARTIAL SEMIREGULARITY: RULED OUT USING HUANG")


if __name__ == "__main__":
    main()
