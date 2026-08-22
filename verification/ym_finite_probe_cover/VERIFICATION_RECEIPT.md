# YM finite probe cover — public replay receipt

Date: 2026-08-13 UTC

Status: **WARNING-FREE PUBLIC LEAN REPLAY OF THE FINITE CORE / NOT YANG–MILLS / FIVE-ALARM OFF.**

Canonical source:

```text
path: verification/ym_finite_probe_cover/YMFiniteProbeCover.lean
Git blob: cadf539a55817683120512cda98d4e3e2c58f744
public head: 81d005bd14a09b3528a86dcf9d749eb8b2c9b33f
```

Replay:

```text
repository: stevemoraco/qs
branch: agent/ym-finite-probe-public-20260813-r2
run: 31699395920
job: 94444599810
runner: Ubuntu 22.04.5 LTS
compiler: AXLE Lean 4.30.0
okay: true
failed declarations: []
Lean errors: []
Lean warnings: []
tool errors: []
tool warnings: []
```

The source-hash gate passed before compiler submission. The workflow rejected `sorry`, `admit`, `sorryAx`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, and `Lean.ofReduceBool` in the exact source.

All seven printed theorem dependency sets were exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The failed-first chronology is preserved:

- the first private workflow attempts never allocated a runner step;
- the first public compiler run found no theorem errors but emitted one deprecation warning for `push_neg`;
- the statement-preserving repair replaced only that tactic by `push Not`;
- the fresh corrected public replay above was warning-free.

The source formalizes only finite logic and real-order bookkeeping for a finite regional probe family. Compactness, continuity of Yang–Mills correlations, transfer operators, RG reachability, continuum OS reconstruction, Euclidean covariance, local fields, asymptotic freedom, and the Clay theorem remain external.

**FIVE-ALARM OFF.**
