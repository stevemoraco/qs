#!/usr/bin/env python3
"""Exact total-gate synthesis certificate for the three-input full adder.

Model
-----
* Three primary Boolean inputs.
* Constants 0 and 1 are available for free.  This strengthens the lower-bound
  model relative to a basis in which constants would have to be generated.
* Each charged gate chooses any two currently available signals (the same
  signal may be chosen twice) and any of the 16 binary Boolean truth tables.
* The two required outputs are parity and majority/carry.

The breadth-first search quotients circuits by their set of available 3-input
truth tables.  This quotient is complete for existence: a one-gate extension
of a circuit depends only on which signal functions are already available.
"""

from __future__ import annotations

from typing import FrozenSet, Iterable, List, Sequence, Tuple

TruthTable = int
State = FrozenSet[TruthTable]


def variable_truth_table(bit: int) -> TruthTable:
    return sum(1 << assignment for assignment in range(8)
               if (assignment >> bit) & 1)


def binary_outputs(left: TruthTable, right: TruthTable) -> Tuple[TruthTable, ...]:
    atoms = [0, 0, 0, 0]
    for assignment in range(8):
        a = (left >> assignment) & 1
        b = (right >> assignment) & 1
        atoms[(a << 1) | b] |= 1 << assignment

    outputs = set()
    for operation in range(16):
        value = 0
        for pair_value in range(4):
            if (operation >> pair_value) & 1:
                value |= atoms[pair_value]
        outputs.add(value)
    return tuple(sorted(outputs))


def target_tables() -> Tuple[TruthTable, TruthTable]:
    inputs = [variable_truth_table(i) for i in range(3)]
    parity = inputs[0] ^ inputs[1] ^ inputs[2]
    majority = sum(
        1 << assignment
        for assignment in range(8)
        if sum((assignment >> i) & 1 for i in range(3)) >= 2
    )
    return parity, majority


def next_states(states: Iterable[State], pair_outputs: Sequence[Sequence[Tuple[TruthTable, ...]]]) -> set[State]:
    result: set[State] = set()
    for state in states:
        signals = sorted(state)
        for i, left in enumerate(signals):
            for right in signals[i:]:
                for output in pair_outputs[left][right]:
                    if output in state:
                        continue
                    result.add(frozenset((*state, output)))
    return result


def verify() -> None:
    inputs = [variable_truth_table(i) for i in range(3)]
    parity, majority = target_tables()

    pair_outputs: List[List[Tuple[TruthTable, ...]]] = [
        [tuple() for _ in range(256)] for _ in range(256)
    ]
    for left in range(256):
        for right in range(left, 256):
            outputs = binary_outputs(left, right)
            pair_outputs[left][right] = outputs
            pair_outputs[right][left] = outputs

    levels: set[State] = {frozenset((*inputs, 0, 255))}
    expected_counts = [1, 33, 828, 20360, 528991]
    observed_counts = [len(levels)]

    assert not any(parity in state and majority in state for state in levels)
    for depth in range(1, 5):
        levels = next_states(levels, pair_outputs)
        observed_counts.append(len(levels))
        assert not any(parity in state and majority in state for state in levels), (
            f"full adder found with at most {depth} gates"
        )

    assert observed_counts == expected_counts, (observed_counts, expected_counts)

    a = inputs[0] ^ inputs[1]
    b = inputs[1] ^ inputs[2]
    product = a & b
    computed_parity = a ^ inputs[2]
    computed_majority = product ^ inputs[1]
    assert computed_parity == parity
    assert computed_majority == majority

    print("level counts:", observed_counts)
    print("EXACT LOWER CERTIFICATE: no <=4-gate full-adder circuit")
    print("EXACT UPPER CERTIFICATE: a 5-gate full-adder circuit exists")
    print("EXACT TOTAL B2 COMPLEXITY: 5")


if __name__ == "__main__":
    verify()
