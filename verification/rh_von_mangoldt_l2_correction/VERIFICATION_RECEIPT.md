# RH von Mangoldt `L²` correction — public replay receipt

Date: 2026-08-13

Status: **LEAN-VERIFIED FINITE CORE / NOT RH / SIX-ALARM OFF.**

## Canonical source

```text
path:
verification/rh_von_mangoldt_l2_correction/RHVonMangoldtL2Correction.lean

Git blob:
1f730eb1fb23fdc49e564e29b1d83bd805ecdd20
```

The source contains five theorem declarations and five `#print axioms` commands. The workflow rejects `sorry`, `admit`, `sorryAx`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, and `Lean.ofReduceBool` before compilation.

## Failed-first chronology

The first hosted compiler run is preserved:

```text
run / job:
31698249583 / 94440902941

source blob:
769150321f1782855b7faee4c22eaf298fd0f49a

verdict:
failure
```

AXLE Lean 4.30 rejected the newer finite-sum binder spelling `∑ i in s`; the errors were parser errors at the two finite sums. No mathematical theorem statement was weakened. Commit `484aa2564abb104d3cb89b580158cd545449b1a3` changed only the binder notation to `∑ i ∈ s`.

The source-only push then failed the deliberately stale exact-blob gate before compilation. Commit `fc26e194dee83f443d620c53cf033213678634ab` updated the workflow to the corrected source blob and triggered a fresh replay.

## Successful warning-free replay

```text
repository:
stevemoraco/qs

branch:
agent/rh-von-mangoldt-l2-correction-verifier-20260813

workflow head:
fc26e194dee83f443d620c53cf033213678634ab

run / job:
31698535435 / 94441797937

runner:
GitHub Actions 1000021083
Ubuntu 22.04.5 LTS

compiler:
AXLE Lean 4.30.0

result:
okay=true
failed declarations=[]
Lean errors=[]
Lean warnings=[]
tool errors=[]
tool warnings=[]

artifact:
9180277800

artifact digest:
sha256:1e2a20f0fda55817503e75a1aae8768b47c02c6bd6fcb3262f360414971e9829
```

Every printed theorem dependency set is exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Verified declarations

1. `square_add_le_two_squares`
2. `weighted_l2_add_le`
3. `weighted_l2_perturbation`
4. `common_scale_budget_transfer`
5. `common_correction_budget_iff`

## Honesty boundary

The source proves only finite real-algebra and finite weighted-sum transfer. It does not define primes, `theta`, `psi`, Mellin transforms, zeta zeros, the explicit formula, the zero-frontier energy abscissa, or RH.

**SIX-ALARM OFF.**
