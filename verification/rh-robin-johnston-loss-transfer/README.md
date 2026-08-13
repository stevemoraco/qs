# Public replay: RH Robin–Johnston loss transfer

This directory is a public kernel-replay mirror of the canonical private source.
It proves a finite order/algebra bridge only; it does **not** prove the Riemann
Hypothesis.

## Exact provenance

- Canonical repository: `stevemoraco/RH-Lean`
- Canonical branch: `agent/rh-robin-johnston-loss-transfer-20260812`
- Canonical source correction commit: `04b5a89c0ce1dd525f5758e9fb6a38bf7e7a16c7`
- Canonical source blob: `60ed502600dc44c8cafc91788fe6bfcd223d089a`
- Public source blob: `60ed502600dc44c8cafc91788fe6bfcd223d089a`
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

The first direct replay found legacy finite-sum syntax rejected by Lean 4.33.0.
The second confirmed that merely opening the old notation scope was insufficient.
The final source uses explicit `Finset.sum` terms, eliminating parser-version
dependence. No theorem statement or mathematical hypothesis was weakened.
