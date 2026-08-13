# Public replay: RH Robin–Johnston loss transfer

This directory is a public kernel-replay mirror of the canonical private source.
It proves a finite order/algebra bridge only; it does **not** prove the Riemann
Hypothesis.

## Exact provenance

- Canonical repository: `stevemoraco/RH-Lean`
- Canonical branch: `agent/rh-robin-johnston-loss-transfer-20260812`
- Canonical branch tip when mirrored: `bbba9cf28cb5ccaacd0ecd0f7881991d1e46d69d`
- Canonical source blob: `c434e998c2a28f2d7323aca3a95bd67cb5610aa5`
- Public source blob: `c434e998c2a28f2d7323aca3a95bd67cb5610aa5`
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
