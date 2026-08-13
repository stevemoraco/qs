#!/usr/bin/env python3
"""Exhaustive small-universe falsifier for the hidden-seed absorption transfer.

This is not a proof of the general theorem.  It exhausts every pair of
positive/core slices on a four-point universe for two seeds, then every global
acceptance set satisfying the theorem's local hypotheses, using exact rational
arithmetic.  Any violation of the residual-incidence or multiplicity-weight
bounds exits nonzero and prints a counterexample.
"""

from fractions import Fraction
from itertools import product
import json
from pathlib import Path

Q = 4
SEEDS = 2
RHO = Fraction(1, 4)


def points(mask: int) -> frozenset[int]:
    return frozenset(i for i in range(Q) if (mask >> i) & 1)


def main() -> None:
    subsets = [points(mask) for mask in range(1 << Q)]
    applicable = 0

    for combo in product(range(1 << Q), repeat=2 * SEEDS):
        positive = [subsets[combo[2 * s]] for s in range(SEEDS)]
        cores = [subsets[combo[2 * s + 1]] for s in range(SEEDS)]

        W = sum(len(h) for h in cores)
        if W == 0:
            continue

        global_positive = frozenset().union(*positive)
        absorbed = sum(len(h & global_positive) for h in cores)
        a = Fraction(absorbed, W)
        if not a < RHO:
            continue

        for accepted in subsets:
            if not global_positive <= accepted:
                continue

            local_ok = all(
                Fraction(len(accepted & cores[s]), 1) >= RHO * len(cores[s])
                for s in range(SEEDS)
            )
            if not local_ok:
                continue

            applicable += 1
            false_positive = accepted - global_positive
            fp_incidence = sum(len(h & false_positive) for h in cores)
            residual_floor = (RHO - a) * W
            if fp_incidence < residual_floor:
                raise AssertionError(
                    ("residual-incidence violation", positive, cores, accepted,
                     W, a, fp_incidence, residual_floor)
                )

            multiplicity = {
                x: sum(x in h for h in cores)
                for x in range(Q)
            }
            denominator = (RHO - a) * W
            edge_mass = sum(
                Fraction(multiplicity[x], 1) for x in false_positive
            ) / denominator
            total_mass = sum(
                Fraction(multiplicity[x], 1)
                for x in range(Q)
                if x not in global_positive
            ) / denominator

            if edge_mass < 1:
                raise AssertionError(
                    ("fractional-edge violation", positive, cores, accepted,
                     a, edge_mass)
                )
            if total_mass > 1 / (RHO - a):
                raise AssertionError(
                    ("fractional-total violation", positive, cores, accepted,
                     a, total_mass)
                )

    result = {
        "status": "PASS",
        "universe_size": Q,
        "seed_count": SEEDS,
        "rho": str(RHO),
        "applicable_configurations": applicable,
        "arithmetic": "fractions.Fraction exact rationals",
        "claim": (
            "Every enumerated configuration satisfying a<rho and the local "
            "core hypotheses satisfies residual incidence >= (rho-a)W, "
            "edge multiplicity mass >= 1, and total mass <= 1/(rho-a)."
        ),
        "scope": "finite exhaustive regression only; not a general proof",
    }

    out = Path(__file__).with_name("hidden-seed-absorption-results.json")
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
