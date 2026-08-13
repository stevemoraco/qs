# Compact positive family — public Lean replay receipt

Date: 2026-08-13 UTC

Status: **WARNING-FREE PUBLIC LEAN REPLAY / FIVE-ALARM OFF.**

Canonical source:

```text
path: verification/compact_positive_family/CompactPositiveFamily.lean
Git blob: 86d20658def1efa2f2b6759a0fdac2b6c2be99f9
public exact-head commit: b0bfea717a038cf6c2684dfaf209b00a49ec713b
```

Replay:

```text
repository: stevemoraco/qs
branch: agent/compact-positive-family-public-20260813
run: 31700796319
job: 94449170028
runner: Ubuntu 22.04.5 LTS
compiler: AXLE Lean 4.30.0
okay: true
failed declarations: []
Lean errors/warnings: [] / []
tool errors/warnings: [] / []
```

The source-hash and forbidden-token gates passed before compiler submission. The sole theorem dependency set was exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The theorem proves that a compact set covered pointwise by strictly positive values of a continuous family of nonnegative real functions admits a finite subfamily whose sum has one uniform positive lower bound on the compact set.

Its Yang–Mills use still requires compactness of the exact terminal interaction set and continuity/nonnegativity/pointwise positivity of the exact OS autocorrelations. It does not construct those analytic inputs or prove a Clay theorem.

**FIVE-ALARM OFF.**
