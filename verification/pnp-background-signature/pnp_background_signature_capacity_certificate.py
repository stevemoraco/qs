#!/usr/bin/env python3
"""Exact finite verifier for round-203 background-signature capacity.

This certificate checks only finite set identities:

* for [n], a support S of size s, a pattern A subset S of size t, and
  weight-b backgrounds B, the count of B with B intersect S = A is
  binom(n-s, b-t);
* the intersection signatures partition every selected background family;
* the largest signature fiber is at least ceil(|W| / 2^s).

It does not verify any circuit-semantic charging theorem or P versus NP.
"""

from __future__ import annotations

from collections import Counter
from itertools import combinations
from math import comb, ceil


def subsets_of_size(n: int, k: int):
    if not 0 <= k <= n:
        return []
    return [frozenset(c) for c in combinations(range(n), k)]


def expected_intersection_count(n: int, s: int, b: int, t: int) -> int:
    k = b - t
    return comb(n - s, k) if 0 <= k <= n - s else 0


def verify_exact_intersection_counts(max_n: int = 11) -> int:
    checked = 0
    for n in range(max_n + 1):
        for s in range(n + 1):
            S = frozenset(range(s))
            for b in range(n + 1):
                backgrounds = subsets_of_size(n, b)
                for t in range(s + 1):
                    for A_tuple in combinations(S, t):
                        A = frozenset(A_tuple)
                        actual = sum(1 for B in backgrounds if B & S == A)
                        expected = expected_intersection_count(n, s, b, t)
                        assert actual == expected, (
                            "intersection count mismatch",
                            n,
                            s,
                            b,
                            A,
                            actual,
                            expected,
                        )
                        checked += 1
    return checked


def deterministic_subfamilies(backgrounds):
    """A fixed collection of hostile/nonuniform subfamilies.

    Exhausting every subfamily would be doubly exponential. These deterministic
    slices test that the partition/pigeonhole implementation does not rely on
    the full symmetric family.
    """

    if not backgrounds:
        return [backgrounds]

    families = [backgrounds]
    families.append(backgrounds[::2])
    families.append(backgrounds[1::2])
    families.append(backgrounds[: max(1, len(backgrounds) // 3)])
    families.append(backgrounds[-max(1, len(backgrounds) // 3) :])

    for modulus in (3, 5, 7):
        family = [
            B
            for B in backgrounds
            if sum((i + 1) * (i + 3) for i in B) % modulus == 0
        ]
        families.append(family)

    out = []
    seen = set()
    for family in families:
        key = tuple(family)
        if key not in seen:
            seen.add(key)
            out.append(family)
    return out


def verify_signature_capacity(max_n: int = 12) -> int:
    checked = 0
    for n in range(max_n + 1):
        for s in range(n + 1):
            S = frozenset(range(s))
            for b in range(n + 1):
                backgrounds = subsets_of_size(n, b)
                for family in deterministic_subfamilies(backgrounds):
                    fibers = Counter(tuple(sorted(B & S)) for B in family)
                    assert sum(fibers.values()) == len(family)
                    assert len(fibers) <= 2**s
                    if family:
                        largest = max(fibers.values())
                        lower = ceil(len(family) / (2**s))
                        assert largest >= lower, (
                            "pigeonhole mismatch",
                            n,
                            s,
                            b,
                            len(family),
                            largest,
                            lower,
                        )
                    checked += 1
    return checked


def main() -> None:
    count_checks = verify_exact_intersection_counts()
    capacity_checks = verify_signature_capacity()
    print(f"exact intersection identities checked: {count_checks}")
    print(f"signature partition/capacity cases checked: {capacity_checks}")
    print("EXACT CERTIFICATE: PASS")
    print("HONESTY: finite combinatorics only; no circuit lower bound and no P != NP.")


if __name__ == "__main__":
    main()
