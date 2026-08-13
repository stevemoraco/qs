# Public replay: RH Robin–Johnston signed loss transfer

This directory is a public kernel-replay mirror of the canonical private source.
It proves finite order/algebra bridges only; it does **not** prove the Riemann
Hypothesis.

## Exact provenance

- Canonical repository: `stevemoraco/RH-Lean`
- Canonical branch: `agent/rh-robin-johnston-loss-transfer-20260812`
- Canonical signed-source commit: `e65c10e0bac55f8f86172486dfe594849430dfe1`
- Canonical source blob: `d2732fa64ec236660c2d584dc2a296f1a870cfc4`
- Canonical source SHA-256: `e5e673addc5559325836f4e75f75c4e45fe7ceb6a4f1792dad159806c6819788`
- Public signed-source commit: `049af3dbf65637d3bb87ffd29eb8a6ea6bd70236`
- Public source blob: `d2732fa64ec236660c2d584dc2a296f1a870cfc4`
- Lean toolchain: `leanprover/lean4:v4.33.0`
- Lean kernel commit: `d8b18978322de05a8f3dba51ef03cf5461676c17`
- Mathlib tag: `v4.33.0`
- Resolved Mathlib commit: `db584cd6d46c92f209a44c0f1c829460d327499d`

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

## Trust boundary

The workflow checks the exact Git blob, rejects `sorry`, `admit`, `sorryAx`,
custom `axiom`, `opaque`, `unsafe`, `native_decide`, and `Lean.ofReduceBool`,
compiles the source directly, parses every embedded `#print axioms` report,
allows only `propext`, `Classical.choice`, and `Quot.sound`, and uploads a replay
receipt.

Every one of the 15 audited exported theorems reported exactly the standard
Mathlib foundation set

```text
[propext, Classical.choice, Quot.sound].
```

## Successful independent replays

The exact public head `f882573470380aee591c252a38b77fe08488a621`
was replayed successfully by two independent GitHub event paths:

```text
push run: 31672813303
job: 94360885776
artifact: 9170384406
artifact digest:
  sha256:d03b64b473d92b73dad13c20ef9ced354c1dfeb0e61dd9a1f24354406601f778

pull-request run: 31672816025
job: 94360891666
artifact: 9170387523
artifact digest:
  sha256:e0c56b0f05d8f25de6d9f428c9f2a693c955bd37ea4ab9ff35ed5c0df027c1b6
```

Both runs checked the same source blob and SHA-256, installed the same pinned
Lean kernel and Mathlib revision, compiled directly, passed the forbidden-trust
scan, passed the parsed axiom allowlist, and uploaded their receipts.

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
7. The final corrected source passed both independent replays with no `sorryAx`
   and no forbidden axiom.

No theorem statement or mathematical hypothesis was weakened in these repairs.
The signed theorem is stronger than the original negative-part formulation.

## Verdict

`LEAN-VERIFIED`: the finite algebraic loss-transfer and block-budget theorems in
this source, under their explicit hypotheses.

`NOT LEAN-VERIFIED`: the logarithmic-integral one-cell premise, either analytic
RH equivalence, the global signed smoothed-Johnston lower bound, and RH itself.
