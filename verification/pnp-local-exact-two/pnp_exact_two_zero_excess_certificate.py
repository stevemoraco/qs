#!/usr/bin/env python3
"""Exact certificate for the local EXACT-2 zero-branching-excess obstruction.

For every n >= 2, construct a normalized fan-in-two B2 circuit with 2n-2 gates
computing

    1[the Hamming weight is positive and even].

Consequently it agrees with EXACT_2 on every input of weight 0, 1, 2, or 3.
The script also verifies the exact critical-path and branching-excess ledger for
this explicit topology.  It is a certificate checker, not a proof of a circuit
lower bound and not a P-versus-NP result.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Callable, Iterable

Bit = int
BoolOp = Callable[[Bit, Bit], Bit]


def op_or(x: Bit, y: Bit) -> Bit:
    return x | y


def op_xor(x: Bit, y: Bit) -> Bit:
    return x ^ y


def op_xnor(x: Bit, y: Bit) -> Bit:
    return 1 ^ (x ^ y)


def op_and(x: Bit, y: Bit) -> Bit:
    return x & y


OPS: dict[str, BoolOp] = {
    "OR": op_or,
    "XOR": op_xor,
    "XNOR": op_xnor,
    "AND": op_and,
}


@dataclass(frozen=True)
class Gate:
    left: int
    right: int
    op: str


@dataclass(frozen=True)
class Circuit:
    input_count: int
    gates: tuple[Gate, ...]

    @property
    def output(self) -> int:
        return self.input_count + len(self.gates) - 1

    @property
    def node_count(self) -> int:
        return self.input_count + len(self.gates)

    def evaluate(self, bits: tuple[Bit, ...]) -> Bit:
        assert len(bits) == self.input_count
        assert all(bit in (0, 1) for bit in bits)
        values = list(bits)
        for gate_index, gate in enumerate(self.gates):
            node = self.input_count + gate_index
            assert 0 <= gate.left < node
            assert 0 <= gate.right < node
            values.append(OPS[gate.op](values[gate.left], values[gate.right]))
        return values[-1]

    def outgoing(self) -> tuple[tuple[int, ...], ...]:
        out: list[list[int]] = [[] for _ in range(self.node_count)]
        for gate_index, gate in enumerate(self.gates):
            target = self.input_count + gate_index
            out[gate.left].append(target)
            out[gate.right].append(target)
        return tuple(tuple(targets) for targets in out)


def append_chain(
    gates: list[Gate], input_count: int, wires: Iterable[int], op: str
) -> int:
    wires = list(wires)
    assert wires
    current = wires[0]
    for wire in wires[1:]:
        gates.append(Gate(current, wire, op))
        current = input_count + len(gates) - 1
    return current


def build_exact_two_baseline(input_count: int) -> Circuit:
    """Build OR(prefix) AND XNOR(XOR(prefix), last)."""
    assert input_count >= 2
    prefix = range(input_count - 1)
    gates: list[Gate] = []
    prefix_or = append_chain(gates, input_count, prefix, "OR")
    prefix_xor = append_chain(gates, input_count, prefix, "XOR")
    last = input_count - 1
    gates.append(Gate(prefix_xor, last, "XNOR"))
    even_total = input_count + len(gates) - 1
    gates.append(Gate(prefix_or, even_total, "AND"))
    return Circuit(input_count, tuple(gates))


def critical_path(circuit: Circuit, input_node: int) -> tuple[int, ...]:
    out = circuit.outgoing()
    path = [input_node]
    current = input_node
    while len(out[current]) == 1:
        current = out[current][0]
        path.append(current)
    return tuple(path)


def verify_semantics(circuit: Circuit) -> None:
    n = circuit.input_count
    # Exhaustive truth-table replay for manageable dimensions.
    for bits in product((0, 1), repeat=n):
        weight = sum(bits)
        actual = circuit.evaluate(bits)
        expected = int(weight > 0 and weight % 2 == 0)
        assert actual == expected, (n, bits, actual, expected)
        if weight <= 3:
            assert actual == int(weight == 2), (n, bits, actual)


def verify_topology(circuit: Circuit) -> dict[str, int]:
    n = circuit.input_count
    g = len(circuit.gates)
    assert g == 2 * n - 2

    out = circuit.outgoing()
    output = circuit.output

    # Normalization: every non-output gate is used, and every input is used.
    for node in range(circuit.node_count):
        if node != output:
            assert len(out[node]) > 0, (n, node, out[node])
    assert len(out[output]) == 0

    paths = tuple(critical_path(circuit, input_node) for input_node in range(n))
    seen: set[int] = set()
    for path in paths:
        assert path
        for node in path:
            assert node not in seen, (n, paths)
            seen.add(node)

    terminals = tuple(path[-1] for path in paths)
    assert terminals[-1] == output
    assert all(len(out[node]) == 2 for node in terminals[:-1])

    type1 = set().union(*(set(path) for path in paths))
    type2_gates = {
        node
        for node in range(n, circuit.node_count)
        if node not in type1
    }

    e1 = sum(len(out[node]) - 2 for node in terminals if node != output)
    e2 = sum(len(out[node]) - 1 for node in type2_gates if node != output)
    o = int(output in type1)

    assert e1 == 0
    assert e2 == 0
    assert o == 1
    assert g == 2 * n - 1 - o + e1 + e2

    wire_count = sum(len(targets) for targets in out)
    assert wire_count == 2 * g
    assert wire_count == 2 * (n - 1) + 1 + (2 * n - 3)

    return {
        "n": n,
        "gates": g,
        "wires": wire_count,
        "critical_paths": len(paths),
        "type1_output_count": o,
        "terminal_excess": e1,
        "outside_excess": e2,
        "total_excess": e1 + e2,
    }


def verify_weight_abstraction(max_n: int = 200) -> None:
    # This independently checks the algebraic semantics without enumerating 2^n inputs.
    for n in range(2, max_n + 1):
        for prefix_weight in range(n):
            for last in (0, 1):
                total = prefix_weight + last
                output = int(prefix_weight > 0 and total % 2 == 0)
                if total <= 3:
                    assert output == int(total == 2)


def main() -> None:
    verify_weight_abstraction()
    ledgers = []
    for n in range(2, 13):
        circuit = build_exact_two_baseline(n)
        verify_semantics(circuit)
        ledgers.append(verify_topology(circuit))

    print("EXACT CERTIFICATE: PASS")
    print("family: OR(prefix) AND XNOR(XOR(prefix), last)")
    print("semantics: positive-even weight; EXACT_2 on weights 0,1,2,3")
    print("gate count: 2n-2 for every n>=2")
    print("branching excess: e1=e2=0; output lies on one critical path")
    print("exhaustive truth tables checked for n=2..12")
    print("weight abstraction checked for n=2..200")
    for ledger in ledgers:
        print(ledger)


if __name__ == "__main__":
    main()
