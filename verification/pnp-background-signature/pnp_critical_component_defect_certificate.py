#!/usr/bin/env python3
"""Exact finite verifier for the critical-component defect identity.

The circuit topology model is a finite acyclic directed wire multigraph:

* vertices 0,...,n-1 are inputs;
* each later vertex is one fan-in-two gate;
* the last gate is the single output;
* a gate's two predecessor wires may have the same source;
* predecessor pairs are enumerated unordered because swapping the two input
  slots does not change any graph quantity checked here.

For every normalized topology in the committed exhaustive range, the script
reconstructs critical paths, their merger components, the T1/T2 partition,
output location, terminal/off-path excess, and every inter-class wire count. It
then checks the exact identities proved in the accompanying note.

It also exhaustively checks the scalar component-error inequality over a much
larger integer range.

HONESTY: this certificate verifies finite graph/arithmetic implementations. It
does not prove Chen--Li--Yang Lemma 4.8, a circuit lower bound, or P != NP.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations_with_replacement, product
from typing import Iterable, Optional, Sequence


@dataclass(frozen=True)
class Invariants:
    n: int
    g: int
    c1: int
    c2: int
    components: int
    output_on_path: int
    terminal_excess: int
    offpath_excess: int


def _critical_path(start: int, outgoing: Sequence[Sequence[int]]) -> tuple[int, ...]:
    path = [start]
    vertex = start
    while len(outgoing[vertex]) == 1:
        vertex = outgoing[vertex][0]
        path.append(vertex)
    return tuple(path)


def _component_count(path_sets: Sequence[set[int]]) -> int:
    count = len(path_sets)
    parent = list(range(count))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x: int, y: int) -> None:
        root_x = find(x)
        root_y = find(y)
        if root_x != root_y:
            parent[root_y] = root_x

    for i in range(count):
        for j in range(i):
            if path_sets[i].intersection(path_sets[j]):
                union(i, j)
    return len({find(i) for i in range(count)})


def verify_topology(
    n: int, gate_parents: Sequence[tuple[int, int]]
) -> Optional[Invariants]:
    """Check one topology; return None when normalization hypotheses fail."""

    g = len(gate_parents)
    vertex_count = n + g
    outgoing: list[list[int]] = [[] for _ in range(vertex_count)]

    for gate_index, (left, right) in enumerate(gate_parents):
        gate = n + gate_index
        assert 0 <= left < gate and 0 <= right < gate
        outgoing[left].append(gate)
        outgoing[right].append(gate)

    output = n + g - 1

    # Single-output normalization and the no-isolated-input hypothesis.
    if any(len(outgoing[input_vertex]) == 0 for input_vertex in range(n)):
        return None
    if any(len(outgoing[gate]) == 0 for gate in range(n, output)):
        return None
    assert len(outgoing[output]) == 0

    paths = [_critical_path(input_vertex, outgoing) for input_vertex in range(n)]
    path_sets = [set(path) for path in paths]
    components = _component_count(path_sets)
    terminals = {path[-1] for path in paths}

    # Intersecting critical paths merge permanently; one terminal per component.
    assert len(terminals) == components

    t1 = set().union(*path_sets)
    t2 = set(range(vertex_count)).difference(t1)
    assert all(vertex >= n for vertex in t2)

    c1 = len(t1)
    c2 = len(t2)
    output_on_path = int(output in t1)

    terminal_excess = sum(
        len(outgoing[terminal]) - 2
        for terminal in terminals
        if terminal != output
    )
    offpath_excess = sum(
        len(outgoing[vertex]) - 1
        for vertex in t2
        if vertex != output
    )
    assert terminal_excess >= 0
    assert offpath_excess >= 0
    total_excess = terminal_excess + offpath_excess

    ell = sum(
        1
        for source in t1
        for target in outgoing[source]
        if target in t1
    )
    e12 = sum(
        1
        for source in t1
        for target in outgoing[source]
        if target in t2
    )
    e21 = sum(
        1
        for source in t2
        for target in outgoing[source]
        if target in t1
    )
    e22 = sum(
        1
        for source in t2
        for target in outgoing[source]
        if target in t2
    )

    # Detailed wire ledger.
    assert e12 == c1 + components - 2 * output_on_path + terminal_excess - ell
    assert e21 == 2 * (c1 - n) - ell
    assert e22 == (
        c2
        - 1
        + output_on_path
        + offpath_excess
        - 2 * (c1 - n)
        + ell
    )
    assert 2 * c2 == e12 + e22

    # Critical-component identity and single-output defect conservation.
    assert c1 + c2 == (
        2 * n
        + components
        - 1
        - output_on_path
        + total_excess
    )
    assert g == (
        n
        + components
        - 1
        - output_on_path
        + total_excess
    )
    assert g - (2 * n - 2) == (
        total_excess
        - (n - components)
        + (1 - output_on_path)
    )

    return Invariants(
        n=n,
        g=g,
        c1=c1,
        c2=c2,
        components=components,
        output_on_path=output_on_path,
        terminal_excess=terminal_excess,
        offpath_excess=offpath_excess,
    )


def enumerate_topologies(n: int, g: int) -> tuple[int, int]:
    predecessor_options = [
        tuple(combinations_with_replacement(range(n + gate_index), 2))
        for gate_index in range(g)
    ]

    enumerated = 0
    normalized = 0
    for gate_parents in product(*predecessor_options):
        enumerated += 1
        if verify_topology(n, gate_parents) is not None:
            normalized += 1
    return enumerated, normalized


def verify_exhaustive_topology_range() -> tuple[int, int]:
    total_enumerated = 0
    total_normalized = 0
    for n in range(1, 5):
        for g in range(1, 6):
            enumerated, normalized = enumerate_topologies(n, g)
            total_enumerated += enumerated
            total_normalized += normalized
            print(
                f"n={n}, g={g}: enumerated={enumerated}, "
                f"normalized={normalized}"
            )
    return total_enumerated, total_normalized


def verify_component_error_inequality(max_r: int = 500) -> int:
    checked = 0
    for r in range(max_r + 1):
        for t in range(r + 1):
            remaining = r - t
            pair_errors = remaining * (remaining - 1) // 2
            assert t + pair_errors >= r - 1
            checked += 1
    return checked


def main() -> None:
    enumerated, normalized = verify_exhaustive_topology_range()
    scalar_checks = verify_component_error_inequality()

    assert enumerated == 3_878_279
    assert normalized == 27_758
    assert scalar_checks == 125_751

    print(f"topologies enumerated: {enumerated}")
    print(f"normalized topologies checked: {normalized}")
    print(f"component-error scalar cases checked: {scalar_checks}")
    print("EXACT CERTIFICATE: PASS")
    print(
        "HONESTY: finite graph/arithmetic certificate only; "
        "no circuit lower bound and no P != NP."
    )


if __name__ == "__main__":
    main()
