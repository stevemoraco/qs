#!/usr/bin/env python3
"""Exhaustive finite check for the PNP orientation-marker firewall.

Checks all 16 binary Boolean gates and all 4^3 unary pre/post wrappers.
No claim about P vs NP is encoded here; this only checks the finite truth-table
classification used by research/pnp-orientation-marker-firewall-20260813.md.
"""

from itertools import product

BOOL = (0, 1)
POINTS = ((0, 0), (0, 1), (1, 0), (1, 1))
UNARY = {
    "C0": (0, 0),
    "C1": (1, 1),
    "ID": (0, 1),
    "NOT": (1, 0),
}
NONCONST = {
    0: (0, 1),  # ID: z -> z xor 0
    1: (1, 0),  # NOT: z -> z xor 1
}

OR = (0, 1, 1, 1)
NAND = (1, 1, 1, 0)
XOR = (0, 1, 1, 0)
XNOR = (1, 0, 0, 1)
ONE = (1, 1, 1, 1)


def eval_binary(table, u, v):
    return table[(u << 1) | v]


def compose(raw, phi, psi, chi):
    return tuple(
        chi[eval_binary(raw, phi[u], psi[v])]
        for u, v in POINTS
    )


def quadratic_tables():
    result = set()
    for a, b, c in product(BOOL, repeat=3):
        result.add(
            tuple(
                (((u ^ a) & (v ^ b)) ^ c)
                for u, v in POINTS
            )
        )
    return result


QUADRATIC = quadratic_tables()
LINEAR = {XOR, XNOR}
ALL_BINARY = list(product(BOOL, repeat=4))


def gate_class(raw):
    if raw in QUADRATIC:
        return "quadratic"
    if raw in LINEAR:
        return "linear"
    return "degenerate"


def main():
    counts = {
        cls: sum(gate_class(raw) == cls for raw in ALL_BINARY)
        for cls in ("quadratic", "linear", "degenerate")
    }
    assert counts == {"quadratic": 8, "linear": 2, "degenerate": 6}

    wrapper_cases = 0
    for raw in ALL_BINARY:
        cls = gate_class(raw)
        for phi, psi, chi in product(UNARY.values(), repeat=3):
            q = compose(raw, phi, psi, chi)
            wrapper_cases += 1

            # OR-positive closure: nonquadratic raw gate + three accepted
            # OR-positive corners forces the constant-one function.
            if cls != "quadratic" and q[1] == q[2] == q[3] == 1:
                assert q == ONE, (raw, cls, phi, psi, chi, q)

            # XOR-positive closure: a quadratic raw gate accepting both
            # off-diagonal corners can only yield OR, NAND, or constant one.
            if cls == "quadratic" and q[1] == q[2] == 1:
                assert q in {OR, NAND, ONE}, (raw, phi, psi, chi, q)

    assert wrapper_cases == 16 * (4 ** 3) == 1024

    # Exact orientation jump. Restrict to nonconstant wrappers, represented
    # by bits p,q,r where z maps to z xor bit. For each quadratic raw gate,
    # OR and NAND each have exactly one such wrapper triple, and OR -> NAND
    # flips both input-orientation bits while preserving the output bit.
    orientation_pairs = 0
    for raw in ALL_BINARY:
        if gate_class(raw) != "quadratic":
            continue

        or_reps = []
        nand_reps = []
        for (p, phi), (q, psi), (r, chi) in product(NONCONST.items(), repeat=3):
            out = compose(raw, phi, psi, chi)
            if out == OR:
                or_reps.append((p, q, r))
            if out == NAND:
                nand_reps.append((p, q, r))

        assert len(or_reps) == 1, (raw, or_reps)
        assert len(nand_reps) == 1, (raw, nand_reps)
        low = or_reps[0]
        high = nand_reps[0]
        assert high == (low[0] ^ 1, low[1] ^ 1, low[2]), (raw, low, high)
        orientation_pairs += 1

    assert orientation_pairs == 8

    print("orientation-marker firewall: PASS")
    print(f"binary gate classes: {counts}")
    print(f"raw gate / unary-wrapper cases checked: {wrapper_cases}")
    print(f"quadratic OR->NAND orientation pairs checked: {orientation_pairs}")


if __name__ == "__main__":
    main()
