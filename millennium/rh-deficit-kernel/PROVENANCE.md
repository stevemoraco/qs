# RH weighted-Chebyshev deficit: independent kernel replay

Date: 2026-08-13

Status: **finite smooth-cell/event-reduction theorem only. NOT RH. SIX-ALARM OFF.**

## Private source

- Repository: `stevemoraco/RH-Lean`
- Draft PR: `#868`
- Original theorem head audited: `496f5b2d80cf9ae67d99340527c6e0400d083a76`
- Current private head carrying the clean interface and receipt: `b387e748b5443dde7f92d56d762de89c81016e0c`
- Original theorem: `lean-worker/RHDeficitExactCriticalPoint.lean`
- Companion root-spec interface: `lean-worker/RHDeficitEventInterface.lean`

The private-repository GitHub Actions attempts attached to PR #868 never received a hosted runner (`runner_id = 0`, zero executed steps), so they supplied no compiler verdict.

## Independent public mirror

- Repository: `stevemoraco/qs`
- Branch: `agent/rh-deficit-kernel-mirror-20260812`
- Draft PR: `#272`
- Exact theorem/toolchain commit: `5467e600feadd2032502c86ab2f9e5a039eb51ec`
- Workflow run: `31678731648`
- Job: `94380107683`

The mirror contains byte-for-byte copies of the two Lean theorem sources plus a standalone pinned Lake project.

## Exact toolchain and commands

- Lean: `v4.31.0`
- Mathlib: `v4.31.0`

The hosted runner completed:

```text
lake update
lake exe cache get
lake build
lake env lean RHDeficitExactCriticalPoint.lean
lake env lean AxiomProbe.lean
lake env lean RHDeficitEventInterface.lean
```

The workflow hard-failed on any occurrence of:

```text
sorryAx
declaration uses sorry
declaration has metavariables
unsolved goals
```

## Kernel result

All sixteen theorem audits were free of `sorryAx`, `sorry`, unresolved metavariables, and unsolved goals.

For the original explicit-root package, the printed axiom sets were:

```text
criticalRoot_spec:
  [propext, Classical.choice, Quot.sound]
criticalRoot_gt_half:
  [propext, Classical.choice, Quot.sound]
slopeNumerator_factor:
  [propext, Classical.choice, Quot.sound]
slopeNumerator_neg_before:
  [propext, Classical.choice, Quot.sound]
slopeNumerator_pos_after:
  [propext, Classical.choice, Quot.sound]
positive_zero_unique:
  [propext, Classical.choice, Quot.sound]
smoothPrimitive_sub:
  [propext, Classical.choice, Quot.sound]
valley_minimum:
  []
```

For the companion root-spec interface:

```text
slopeNumerator_factor_from_root:
  [propext, Classical.choice, Quot.sound]
root_gt_half:
  [propext, Classical.choice, Quot.sound]
slopeNumerator_neg_before:
  [propext, Classical.choice, Quot.sound]
slopeNumerator_pos_after:
  [propext, Classical.choice, Quot.sound]
positive_root_unique:
  [propext, Classical.choice, Quot.sound]
smoothPrimitive_sub_raw:
  [propext, Classical.choice, Quot.sound]
intervalIncrement_add:
  []
valley_minimum:
  []
```

The dependency probe for `Real.sq_sqrt`, `Real.sqrt_nonneg`, `Real.log_div`, and the arithmetic tactics reported only the same accepted foundational/Mathlib axiom surface and no `sorryAx`.

## Exact theorem surface

The replay kernel-closes only the finite knot-free-cell layer:

1. the positive quadratic root of the smooth-cell slope numerator;
2. its equation, location above `1/2`, uniqueness, and exact slope signs;
3. exact smooth-cell propagation of the deficit;
4. the interval-increment cocycle;
5. reduction of each continuous cell minimum to its event/critical candidate.

It does **not** formalize or prove:

- the von Mangoldt staircase and endpoint conventions;
- the identification of the analytic deficit with the Lean cell parameters;
- Suzuki's Weil/screw-function criterion;
- Landau's nonnegative-Laplace argument;
- the claimed equivalence between eventual deficit positivity and RH;
- the missing uniform arithmetic positivity theorem over every sufficiently late event.

Therefore this is a durable finite theorem and independent replay receipt, not a Clay-proof certificate.

```text
Lean kernel replay: PASS
sorry/admit/sorryAx/metavariables: NONE OBSERVED
accepted axiom surface: propext, Classical.choice, Quot.sound where printed
Clay theorem closed: NO
SIX-ALARM: OFF
```
