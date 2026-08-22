# Navier–Stokes bounded-reservoir orbit forces a fixed cubic window

**Date:** 2026-08-12 America/Denver / 2026-08-13 UTC  
**Scope:** conditional theorem extracted from the standard pressure recurrence and energy compactness. This is not a regularity proof or blowup construction.

## Statement

Consider an admissible dyadic chain for a suitable weak solution and the scale-critical quantities

\[
A_k,\quad E_k,\quad C_k,\quad D_k,\quad B_k=A_k+C_k+D_k.
\]

Assume there are constants `epsilon > 0` and `K < infinity` such that for every sufficiently large `k`,

\[
C_k+D_k\ge\varepsilon,
\qquad
B_k\le K.
\]

The first condition is the persistent Caffarelli–Kohn–Nirenberg badness branch. The second defines the bounded-reservoir lane.

Then, after choosing the fixed scale ratio `theta` sufficiently small depending only on `K`, `epsilon`, and the standard pressure constant, there exist

\[
\delta=\delta(K,\varepsilon,\theta)>0,
\qquad
M=M(K,\varepsilon,\theta)<\infty
\]

such that:

1. every pair of consecutive sufficiently small scales contains an index `j` with
   \[
   C_j>\delta;
   \]
2. after rescaling the scale-`j` cylinder to a unit cylinder, a fixed spatial frequency window `|xi| <= M` carries a definite amount of cubic spacetime mass:
   \[
   \|P_{\le M}u^{(j)}\|_{L^3(Q_1)}^3\ge\frac\delta8.
   \]

The cutoff `M` is independent of `j`. Thus spatial moving-window growth is unnecessary for the velocity-cubic sector of a bounded-reservoir bad orbit.

## Step 1: pressure recurrence forces cubic activity in every adjacent pair

Yu's full-ledger paper records the standard pressure decay recurrence

\[
D_{k+1}\le aD_k+bC_k,
\qquad
a=C_P\theta,
\qquad b=C_P\theta^{-2}.
\]

Choose `theta` so that

\[
aK<\frac\varepsilon4.
\]

Then choose `delta > 0` so small that

\[
aK+b\delta+\delta<\varepsilon.
\]

Suppose both `C_k <= delta` and `C_{k+1} <= delta`. Since `D_k <= K`,

\[
D_{k+1}\le aK+b\delta,
\]

and therefore

\[
C_{k+1}+D_{k+1}
\le
\delta+aK+b\delta
<\varepsilon,
\]

contradicting persistent CKN badness. Hence

\[
\boxed{
\delta<C_k\quad\text{or}\quad\delta<C_{k+1}
}
\]

for every large `k`.

This finite implication is kernel-checked in Lean as

`NavierStokesPressureRecurrence.cubicEventInEveryAdjacentPair`.

## Step 2: the reservoir bound gives a uniform dissipation bound

Yu's local energy transition and transition-closure estimates give

\[
A_k+E_k
\lesssim_\theta
\Lambda_{k-1}+\Phi_{k-1}+2\Pi_{k-1},
\]

with

\[
\Lambda_{k-1}\lesssim_\theta A_{k-1},
\qquad
\Phi_{k-1}\lesssim_\theta C_{k-1},
\qquad
\Pi_{k-1}\lesssim_\theta
C_{k-1}^{1/3}D_{k-1}^{2/3}.
\]

If `B_{k-1} <= K`, every term on the right is bounded by a constant depending only on `K` and `theta`. Thus

\[
\boxed{E_k\le K_E(K,\theta)}
\]

uniformly along the bounded-reservoir orbit.

After the Navier–Stokes rescaling to the unit cylinder,

\[
\operatorname*{ess\,sup}_t\|u^{(k)}(t)\|_2^2\le K,
\qquad
\int_{Q_1}|\nabla u^{(k)}|^2\le K_E.
\]

## Step 3: cubic high-frequency tails decay uniformly

Let `U` be any normalized velocity field on a unit periodic cylinder with

\[
\operatorname*{ess\,sup}_t\|U(t)\|_2^2\le A,
\qquad
\int|\nabla U|^2\le E.
\]

For the smooth high-frequency projection `W=P_{>M}U`, the spectral Poincare estimate gives

\[
\|W\|_{L^2_{t,x}}\le M^{-1}E^{1/2}.
\]

The energy-Sobolev estimate gives

\[
\|W\|_{L^{10/3}_{t,x}}
\lesssim
A^{1/5}E^{3/10}.
\]

Interpolating `L^3` between `L^2` and `L^{10/3}` with weight `1/6` on `L^2`,

\[
\|W\|_{L^3}^3
\le
\|W\|_{L^2}^{1/2}
\|W\|_{L^{10/3}}^{5/2}
\lesssim
\boxed{M^{-1/2}A^{1/2}E}.
\]

This exponent is the key point. Unlike selected-time `L^2` energy, cubic **spacetime** mass cannot hide in arbitrarily high frequencies while both the critical energy and integrated dissipation remain bounded.

At a cubic event `C_j=||u^{(j)}||_3^3 > delta`, choose one fixed `M` so that

\[
C M^{-1/2}K^{1/2}K_E\le\frac\delta8.
\]

Then

\[
\|P_{>M}u^{(j)}\|_3\le\frac12\delta^{1/3},
\]

and the triangle inequality gives

\[
\boxed{
\|P_{\le M}u^{(j)}\|_3^3\ge\frac\delta8.
}
\]

The same `M` works at every cubic event in the bounded-reservoir orbit.

## Hostile audit

### What this theorem removes

It removes one proposed source of moving-window degeneration:

\[
\text{bounded }A,E
+
\text{persistent }C+D\text{ badness}
\not\Rightarrow
\text{spatial frequency escape of all velocity activity}.
\]

The exact shear initial-layer counterexample does not contradict this result. That family preserves selected-time `L^2` energy but its cubic spacetime mass tends to zero as the frequency tends to infinity.

### What it does not remove

The theorem does not prove regularity because it does not yet establish:

1. a uniform local-to-periodic chart preserving the captured cubic component;
2. that the captured low-frequency cubic mass lies outside the cleaning quotient;
3. quantitative pressure, flux, covariance, and trace observability on the localized package;
4. negligible cutoff and harmonic-pressure errors;
5. compatible cleanings across scales;
6. any control of the **unbounded-reservoir lane** `B_k -> infinity`.

The fixed-window positive-cone theorem in Yu's paper is finite-dimensional and conditional on its separation assumptions. The result here supplies a fixed velocity window only in the bounded-reservoir branch; it does not supply the remaining clean-to-local transfer hypotheses.

## New branch split

A hypothetical singular orbit now splits into two sharper mechanisms.

### Bounded reservoir

\[
\sup_k B_k<\infty.
\]

Then cubic events occur in every adjacent scale pair and a fixed velocity-frequency window detects them. The highest gate is localized quotient visibility and cross-scale gluing, not moving-window growth.

### Unbounded reservoir

\[
\limsup_kB_k=\infty.
\]

Then the obstruction is genuine critical-norm growth/concentration. The highest-leverage tools are quantitative blowup-rate and physical-space concentration propagation, including the Barker and Barker–Popkin machinery.

This is a more useful dichotomy than treating every potential singularity as an arbitrary moving-window phantom.

## Exact next theorem

The bounded lane is reduced to

\[
\boxed{\texttt{NS-FIXED-CUBIC-LOCAL-TO-CLEAN-COERCIVITY}.}
\]

For the fixed window `M(K,epsilon,theta)`, prove that a localized rescaled packet with low-mode cubic mass at least `delta/8` has a uniformly positive quotient distance or a uniformly positive pressure/flux/energy observation after all cutoff, harmonic-pressure, gauge, and reproduction errors are included.

A valid theorem must be uniform in the scale index and must not silently convert cubic mass into a signed linear observation.

## Status

No official three-dimensional Navier–Stokes existence/smoothness theorem or finite-time blowup construction is obtained. No Millennium alarm condition is met.
