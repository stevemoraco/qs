# Public replay: RH Robin–Johnston loss transfer

This directory is a public kernel-replay mirror of the canonical private source.
It proves a finite order/algebra bridge only; it does **not** prove the Riemann
Hypothesis.

## Exact provenance

- Canonical repository: `stevemoraco/RH-Lean`
- Canonical branch: `agent/rh-robin-johnston-loss-transfer-20260812`
- Canonical source correction commit: `79330f3e1d925b8caea02bba32fd21c4961ba8a3`
- Canonical source blob: `6f68558a5ec9ed9997d0b4f7598d68e1046c9563`
- Public source blob: `6f68558a5ec9ed9997d0b4f7598d68e1046c9563`
- Lean toolchain: `leanprover/lean4:v4.33.0`
- Mathlib revision: `v4.33.0`

## Verified source scope

The module formalizes:

1. negative-part loss transfer from a buffered lower bound;
2. the exact weight conversion under `J = L*z`;
3. finite block summation;
4. positivity from a strict cumulative block budget.

The source deliberately takes the one-cell logarithmic-integral estimate as a
premise. It does not formalize the prime-cell calculus, Johnston's RH criterion,
or RH.

## Replay gate

The workflow checks the exact Git blob, rejects `sorry`, `admit`, `sorryAx`,
custom `axiom`, `opaque`, `unsafe`, `native_decide`, and `Lean.ofReduceBool`,
compiles the source directly, parses every requested `#print axioms` report,
allows only `propext`, `Classical.choice`, and `Quot.sound`, and uploads a replay
receipt.

The first direct replay reached Lean 4.33.0 and correctly rejected the original
source because finite-sum notation lacked `open scoped BigOperators`. The
canonical and public sources were corrected byte-for-byte; no theorem statement
or hypothesis was weakened.
