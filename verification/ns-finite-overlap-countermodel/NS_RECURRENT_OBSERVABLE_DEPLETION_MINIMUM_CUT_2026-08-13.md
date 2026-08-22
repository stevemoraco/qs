# Navier–Stokes recurrent observable depletion minimum cut

**Date:** 2026-08-13  
**Scope:** conditional rigidity theorem for the bounded-reservoir recurrent branch; not a Navier–Stokes regularity proof or blowup construction.

## 1. Input from the bounded-reservoir reduction

The companion branch reduces a hypothetical centered singular orbit with uniformly bounded critical reservoir to a nonzero recurrent state `X_*` in a compact local topology. Concretely, for a fixed parabolic scale shift `T`, there are integers

\[
n_j\to\infty
\]

such that

\[
T^{n_j}X_*\to X_*
\]

strongly in local `L^3` for velocity, with the compatible weak pressure topology.

The present note isolates the smallest additional theorem that would contradict this recurrence.

## 2. Recurrence supplies a fixed positive observation floor

Because the velocity component of `X_*` is nonzero in local `L^3`, duality gives a smooth compactly supported vector test `g` with

\[
\mathcal O(X_*):=
\left|\iint g\cdot U_*\right|>0.
\]

The map

\[
\mathcal O(X)=\left|\iint g\cdot U\right|
\]

is continuous in the strong local `L^3` topology. Hence recurrence gives, for all sufficiently large `j`,

\[
\mathcal O(T^{n_j}X_*)
\ge
\frac12\mathcal O(X_*)
=:\delta>0.
\]

This removes the vanishing-threshold problem entirely. The return subsequence carries one fixed positive observable floor.

## 3. Exact conditional contradiction

Suppose the selected return intervals admit nonnegative quantities

\[
B_j\ge0,
\qquad
A_j\ge0,
\qquad
e_j\in\mathbb R,
\]

and constants `c>0`, `q>0` such that

\[
B_{j+1}+cA_j\le B_j+e_j,
\]

\[
A_j\ge \mathcal O(T^{n_j}X_*)^q,
\]

and the cumulative errors are uniformly bounded above:

\[
\sup_N\sum_{j<N}e_j<\infty.
\]

Then, after discarding finitely many initial returns,

\[
A_j\ge\delta^q>0.
\]

Summing the one-step inequality gives

\[
B_N+c\sum_{j<N}A_j
\le
B_0+\sum_{j<N}e_j.
\]

The right side stays bounded while the left side grows at least linearly in `N`. Contradiction.

The Lean theorem `recurrentObservableDepletionImpossible` formalizes the complete scalar argument, including the Archimedean choice of a finite prefix that overruns the budget.

## 4. Claimant / critic / rebuilder

### Claimant

A recurrent singular state cannot survive a strict scale-transition depletion law. Recurrence turns any continuous positive local observation into infinitely many fixed-size charges, so neither first-threshold attainment nor a diagonal `tau_j -> 0` is needed.

### Critic

The observation is easy. The depletion cocycle is the problem.

Ordinary critical energy does not pay a fixed amount at every geometric scale. A radius-`r` critical packet has physical energy and dissipation of order `r`, and

\[
\sum_{k\ge0}2^{-k}<\infty.
\]

Local energy identities also contain pressure, flux, and cutoff terms that may be order one on every selected interval. A per-return bound `e_j <= C` is useless; the cumulative error must be uniformly bounded or summable.

The Lean theorem `unitErrorFundsPerpetualUnitReturns` gives the minimal countermodel: zero budget, unit activity, and unit error at every return satisfy the one-step inequality forever.

### Rebuilder

The exact analytic target is therefore not “find a positive observer.” It is:

## NS-RETURN-INTERVAL-OBSERVABLE-DEPLETION

For the recurrent ancient solution extracted from a bounded centered critical reservoir, construct a scale-transition budget and a smooth local observer such that, on the actual recurrence-return intervals,

\[
B_{j+1}
+c\left|\iint g\cdot U_j\right|^q
\le
B_j+e_j,
\]

with

\[
B_j\ge0,
\qquad c,q>0
\]

uniform in `j`, and

\[
\sup_N\sum_{j<N}e_j<\infty.
\]

The budget must be a genuinely global finite capacity or a monotone Lyapunov quantity. Reusing the same local energy, pressure, or source charge across nested scales is forbidden unless a fresh-charge or Carleson theorem is proved.

## 5. Consequence for the proof DAG

The bounded-reservoir branch now has the exact form

\[
\boxed{
\begin{aligned}
&\text{hypothetical singularity}\
&\Longrightarrow\text{compact recurrent ancient scale orbit}\
&\Longrightarrow\text{fixed positive local observation on infinitely many returns}\
&\xRightarrow{\text{one depletion cocycle}}\bot.
\end{aligned}}
\]

Thus the minimum cut is one equation-level cocycle theorem, not a parameter choice and not a vanishing-threshold compactness argument.

The unbounded-reservoir branch remains separate and requires quantitative critical concentration or blowup-rate control.

## 6. Lean and trust boundary

File: `NavierStokesRecurrentDepletionCocycle.lean`.

Kernel-checked declarations:

- `finiteReturnDepletion`;
- `recurrentFixedChargeDepletionImpossible`;
- `recurrentObservableDepletionImpossible`;
- `unitErrorFundsPerpetualUnitReturns`.

Fresh hosted replay of exact head `013763ca41efb56cfa919c732a1d01fd32fee8b0`:

- workflow run `31699740464`;
- job `94445737763`;
- Lean `4.32.1`;
- Mathlib commit `520045ab14e26149ee970e2e617ca04b09bde5d6`;
- evidence artifact `9180807424`;
- artifact digest `sha256:ed05e3f352863a063180ca6a839aa29bd1f425e6ed3323b13e4858e0efb0dbac`;
- reported axioms are subsets of `propext`, `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, `sorryAx`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, or `Lean.ofReduceBool`.

The Lean file proves only the finite scalar depletion core. It does not formalize suitable weak solutions, recurrence extraction, the observer-separation theorem, or the missing PDE cocycle.

## Status

No official three-dimensional Navier–Stokes regularity theorem or finite-time blowup construction is proved. No Millennium alarm condition is met.
