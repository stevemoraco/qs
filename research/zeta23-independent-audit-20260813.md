# Zeta23 external audit: pinned kernel replay and import opportunity

Date: 2026-08-13  
Status: independent replay in progress; not RH and not a Clay result.

## Object under audit

Anthropic released:

- paper: [More Than Two Thirds of the Zeros of the Riemann Zeta Function Lie on the Critical Line](https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf);
- Lean repository: [anthropics/zeta-23-lean](https://github.com/anthropics/zeta-23-lean);
- audited commit: `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`;
- audited tree: `724f95ba42747dcf66aaebb68efd1316df6debac`;
- toolchain: `leanprover/lean4:v4.33.0-rc2`;
- pinned Mathlib: `51e6992efd06126df61a496bebf8f49482a4e129`.

The headline comparator statement is the exact epsilon-form

[
orallarepsilon>0;exists T_0;orall Tge T_0,qquad
(2/3-arepsilon)N(T,2T)le N_0^*(T,2T),
]

where the left side counts Mathlib `riemannZeta` zeros in the open critical
strip with analytic multiplicity and the right side counts distinct zeros on
(Re s=1/2). The multiplicity topic states the stronger simple-zero form with
(N_0^s), and a (5/6) distinct-zero bound.

None of these statements is RH. A density-one exceptional set can still
contain zeros arbitrarily far to the right.

## Trust boundary reconstructed so far

The trusted definition layer
`comparator/ChallengeDeps.lean` imports Mathlib only and defines:

- `IsNontrivialZero ρ := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1`;
- `zeroMult ρ := (analyticOrderAt riemannZeta ρ).toNat`;
- `Ncount` by `finsum`, and the distinct/on-line counts by `Set.ncard`.

The solution cone proves local finiteness of every ordinate window and proves
that analytic order at a nontrivial zero is finite and positive before these
totalized operations are used. Thus the obvious `finsum=0` and
`toNat ⊤=0` vacuity attacks do not survive source inspection.

The project packages the literature inputs as explicit structure fields, but
the unconditional headline theorem constructs that structure internally:
the zeta seam, Weil explicit formula, Riemann--von Mangoldt estimate,
Chebyshev--Mertens bounds, Montgomery--Vaughan inequality, and Gamma estimates
are all connected by named theorems rather than supplied as headline
parameters.

This is a source-level finding only until fresh replay completes.

## Independent replay

The workflow in this PR:

1. clones the exact external commit and records its tree, toolchain, Mathlib
   pin, and hashes of the trusted definitions/statements/solution;
2. lexically strips nested Lean comments and strings, then rejects
   `sorry`, `admit`, `sorryAx`, `axiom`, `opaque`, `unsafe`,
   `native_decide`, and `Lean.ofReduceBool` throughout `Zeta23/`,
   `Solution*`, and `ChallengeDeps*`;
3. deliberately excludes the trusted challenge files, whose theorem bodies
   are `sorry` placeholders by comparator design;
4. builds the pinned headline proof cone from a fresh clone;
5. recompiles exact semantic canaries against the Mathlib-only definitions;
6. replays all 33 upstream headline axiom reports and rejects any dependency
   outside `propext`, `Classical.choice`, and `Quot.sound`;
7. uploads source metadata and complete logs even on failure.

This is not yet a full independent `leanprover/comparator` sandbox replay or
a `nanoda` replay. Those remain separate gates. A clean Lean build checks
kernel acceptance and the stated axiom surface, not the human novelty claim.

## Claimant / critic / rebuilder

**Claimant.** If the artifact survives, inherit its already-formalized explicit
formula, zero counting, Gamma estimates, and off-line-zero linear algebra
instead of rebuilding those bridges in RH-Lean.

**Critic.** A clean axiom report can miss a weakened or vacuous theorem
statement, totalized infinite sums, hidden structure parameters, or a mismatch
between paper constants and comparator constants. The human proof can also
contain a conceptual mismatch that the Lean theorem faithfully formalizes.

**Rebuilder.** Keep only:

- exact comparator definitions read independently of `Zeta23/`;
- fresh kernel and axiom evidence;
- source-closed analytic inputs whose public theorem types match the intended
  mathematics;
- reusable modules imported behind a new RH-Lean semantic adapter, never by
  copying a headline theorem into an assumption.

## Next hostile gates

1. Complete the fresh build and preserve hashes/logs.
2. Run comparator from a clean sandbox and, separately, an independent kernel.
3. Audit the paper's zero-side inertia/rank argument and every
   finite-window-to-asymptotic passage.
4. Check the multiplicity constants against the exact challenge statements.
5. Test whether the infrastructure can formalize the dyadic-theta Mellin
   criterion without introducing an RH-equivalent hypothesis.

**SIX-ALARM: OFF.**
