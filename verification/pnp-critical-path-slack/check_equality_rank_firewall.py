#!/usr/bin/env python3
"""Exhaustive finite checker for PNPEqualityRankFirewallFinite.

This does not replace the Lean kernel proof.  It independently enumerates the
four unary Boolean maps, checks rank multiplicativity, and then checks every
fixed pair of branch maps for two occurrences of a live variable against all
low/high branch-independent unary contexts.
"""

from itertools import product


def evaluate(f: int, x: int) -> int:
    """Unary truth table f in 0..3; bit x is f(x)."""
    return (f >> x) & 1


def compose(f: int, g: int) -> int:
    """f after g."""
    return evaluate(f, evaluate(g, 0)) | (evaluate(f, evaluate(g, 1)) << 1)


def nonconstant(f: int) -> bool:
    return (f & 1) != ((f >> 1) & 1)


def chain5(c0: int, t1: int, c1: int, t2: int, c2: int) -> int:
    return compose(c2, compose(t2, compose(c1, compose(t1, c0))))


def main() -> None:
    for f, g in product(range(4), repeat=2):
        assert nonconstant(compose(f, g)) == (nonconstant(f) and nonconstant(g))

    applicable_fixed = 0
    high_context_cases = 0

    for t10, t11, t20, t21 in product(range(4), repeat=4):
        low_exists = any(
            nonconstant(chain5(l0, t10, l1, t20, l2))
            and nonconstant(chain5(l0, t11, l1, t21, l2))
            for l0, l1, l2 in product(range(4), repeat=3)
        )
        if not low_exists:
            continue

        applicable_fixed += 1
        for h0, h1, h2 in product(range(4), repeat=3):
            branch0 = nonconstant(chain5(h0, t10, h1, t20, h2))
            branch1 = nonconstant(chain5(h0, t11, h1, t21, h2))
            high_context_cases += 1
            assert branch0 == branch1, (
                (t10, t11, t20, t21),
                (h0, h1, h2),
                branch0,
                branch1,
            )

    print("composition_pairs=16")
    print(f"applicable_fixed_transition_quadruples={applicable_fixed}")
    print(f"high_context_cases_checked={high_context_cases}")
    print("status=PASS")


if __name__ == "__main__":
    main()
