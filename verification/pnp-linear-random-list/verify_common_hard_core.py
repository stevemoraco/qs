#!/usr/bin/env python3
"""Finite regression for the PNP common-hard-core counting constants.

Discovery/regression only.  This is not a proof of Chernoff, circuit counting,
NP-uniformity, Chen--Li--Yang, or P versus NP.
"""

from fractions import Fraction
from math import comb, exp, log, log2


def circuit_log2_upper(n: int, g: int) -> float:
    # Same elementary description overcount as verify.py on the parent branch.
    return (
        log2(g + 1)
        + log2(n + g + 2)
        + g * (4 + 2 * log2(n + g + 2))
    )


def check_power(e: int) -> None:
    n = 1 << e
    L = e
    M = 256 * n * L
    Q = comb(n, 4)
    g = 3 * n

    assert M % 4 == 0
    assert Q >= Fraction(n**4, 192)

    log2_K = circuit_log2_upper(n, g)
    assert log2_K <= 10 * n * L

    # Per-circuit bad probability <= exp(-M/16).
    # Compare logs, avoiding numerical underflow.
    log_union_bad = log(2) * log2_K - M / 16
    assert log_union_bad < -9 * n * L

    collision = Fraction(comb(2 * M, 2), Q)
    crude_collision = Fraction(2 * M * M * 192, n**4)
    assert collision < crude_collision
    assert crude_collision < Fraction(3, 25)  # < 0.12

    # Even the much looser sum is strictly below one.
    assert float(collision) + exp(min(log_union_bad, -1000.0)) < 1.0

    print(
        f"n=2^{e:<2}  log2K/(nL)={log2_K/(n*L):.6f}  "
        f"union-log-margin/(nL)={-log_union_bad/(n*L):.6f}  "
        f"collision={float(collision):.6e}"
    )


def main() -> None:
    for e in range(18, 31):
        check_power(e)
    print("PASS: finite common-hard-core constants 2^18..2^30")


if __name__ == "__main__":
    main()
