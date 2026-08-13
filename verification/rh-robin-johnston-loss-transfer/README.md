# Public replay: RH Robin–Johnston signed loss transfer

This directory is a public kernel-replay mirror of the canonical private source.
It proves finite order/algebra bridges only; it does **not** prove the Riemann
Hypothesis.

## Exact provenance

- Canonical repository: `stevemoraco/RH-Lean`
- Canonical branch: `agent/rh-robin-johnston-loss-transfer-20260812`
- Canonical signed-source commit: `e65c10e0bac55f8f86172486dfe594849430dfe1`
- Canonical source blob: `d2732fa64ec236660c2d584dc2a296f1a870cfc4`
- Public signed-source commit: `049af3dbf65637d3bb87ffd29eb8a6ea6bd70236`
- Public source blob: `d2732fa64ec236660c2d584dc2a296f1a870cfc4`
- Lean toolchain: `leanprover/lean4:v4.33.0`
- Mathlib revision: `v4.33.0`

## Source scope

The module formalizes:

1. antitonicity of negative part and the sharp loss inherited from any lower bound;
2. conversion of a signed buffered lower bound into the coarser negative-part bound;
3. the exact signed and negative-part weight conversions under `J = L*z`;
4. finite unsigned-charge and signed block summation;
5. positivity from either strict finite-block budget.

The source deliberately takes the one-cell logarithmic-integral estimate as a
premise. It does not formalize the prime-cell calculus, Johnston's RH criterion,
Robin's RH criterion, or RH.

## Replay gate

The workflow checks the exact Git blob, rejects `sorry`, `admit`, `sorryAx`,
custom `axiom`, `opaque`, `unsafe`, `native_decide`, and `Lean.ofReduceBool`,
compiles the source directly, parses every embedded `#print axioms` report,
allows only `propext`, `Classical.choice`, and `Quot.sound`, and uploads a replay
receipt.

## Hostile replay history

1. The first direct replay rejected legacy finite-sum syntax under Lean 4.33.0.
2. The second showed that opening the old notation scope was insufficient.
3. Explicit `Finset.sum` terms then compiled cleanly byte-for-byte.
4. The first axiom audit correctly failed because a separate report file tried
   to import a module for which direct compilation had not emitted an `.olean`.
5. Reports were embedded in the exact source, removing that search-path dependency.
6. The signed upgrade exposed an addition-order elaboration mismatch; replacing
   the brittle term with kernel-checked linear arithmetic preserved the theorem
   statement exactly.

No theorem statement or mathematical hypothesis was weakened in these repairs.
The signed theorem is stronger than the original negative-part formulation.

Status at this commit: final fixed-source replay pending. No green label is
inherited until the exact run and receipt are inspected.
