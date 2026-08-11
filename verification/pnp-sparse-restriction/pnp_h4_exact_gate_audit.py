#!/usr/bin/env python3
"""Finite verifier for the 4-variable marker gadget.

The marker seed at input length four accepts exactly the strings of Hamming
weight one or four.  This script checks the explicit seven-gate full-binary-
basis circuit recorded in the companion theorem note and prints the complete
truth table.  It is a finite falsifier/verifier, not a proof about arbitrary
input length and not a proof of P versus NP.
"""

from __future__ import annotations

from itertools import product


def target(x: tuple[int, int, int, int]) -> int:
    return int(sum(x) in (1, 4))


def circuit(x: tuple[int, int, int, int]) -> int:
    x0, x1, x2, x3 = x
    g0 = int(not (x0 or x3))        # NOR(x0,x3)
    g1 = int(x2 or g0)              # OR(x2,g0)
    g2 = x1 ^ x2                    # XOR(x1,x2)
    g3 = x0 ^ g1                    # XOR(x0,g1)
    g4 = g0 ^ g2                    # XOR(g0,g2)
    g5 = int(not (x3 ^ g3))         # XNOR(x3,g3)
    g6 = int(not (g4 or g5))        # NOR(g4,g5)
    return g6


def main() -> None:
    truth = 0
    rows: list[str] = []
    for bits in product((0, 1), repeat=4):
        want = target(bits)
        got = circuit(bits)
        if got != want:
            raise AssertionError((bits, want, got))
        index = sum(bit << i for i, bit in enumerate(bits))
        truth |= got << index
        rows.append(f"{''.join(map(str, bits))}: {got}")

    expected = 0x8116
    if truth != expected:
        raise AssertionError((hex(truth), hex(expected)))

    print("verified all 16 inputs")
    print(f"truth_table_hex=0x{truth:04x}")
    print("gate_count=7")
    print("\n".join(rows))


if __name__ == "__main__":
    main()
