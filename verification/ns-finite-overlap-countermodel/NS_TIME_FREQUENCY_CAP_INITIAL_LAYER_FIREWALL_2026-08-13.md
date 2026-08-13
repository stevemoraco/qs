# Navier–Stokes time-frequency cap: exact initial-layer firewall

**Date:** 2026-08-12 America/Denver / 2026-08-13 UTC  
**Scope:** exact smooth Navier–Stokes counterexample to a naive fixed-window extraction theorem, finite Lean scaling core, and best salvage. This is not a regularity proof or blowup construction.

## Claim under attack

A tempting repair of the finite-window anti-phantom route is:

> A scale-normalized package with nonzero selected-time kinetic energy and bounded integrated enstrophy must place a fixed positive amount of energy in one frequency window whose size depends only on those two bounds.

This claim would let Yu's fixed-window positive-cone observability theorem operate with a scale-uniform active window and would try to charge window growth to the dissipation tax.

The claim is false, even for exact globally smooth solutions of the unforced three-dimensional Navier–Stokes equations.

## Exact smooth counterexample

Work on the flat three-torus. For every integer `N >= 1`, choose the normalized divergence-free shear mode

\[
e_N(x)=c\,(\sin(Nx_2),0,0),
\qquad \|e_N\|_{L^2(\mathbb T^3)}=1,
\]

and define

\[
u_N(x,t)=e^{-N^2t}e_N(x),
\qquad p_N=0,
\qquad t\ge0.
\]

Because `e_N` depends only on `x_2` and points in the `x_1` direction,

\[
\nabla\cdot e_N=0,
\qquad
(e_N\cdot\nabla)e_N=e_{N,1}\partial_1e_N=0.
\]

Also `Delta e_N=-N^2e_N`. Therefore

\[
\partial_tu_N-\Delta u_N+(u_N\cdot\nabla)u_N+\nabla p_N=0
\]

exactly. This is not an arbitrary compactness sequence or an approximate PDE model; it is a family of classical Navier–Stokes solutions.

Its energy quantities are

\[
\sup_{t\ge0}\|u_N(t)\|_2^2=1,
\]

\[
\int_0^\infty\|\nabla u_N(t)\|_2^2\,dt
=
\int_0^\infty N^2e^{-2N^2t}\,dt
=\frac12,
\]

and

\[
\int_0^\infty\|u_N(t)\|_2^2\,dt
=\frac1{2N^2}\longrightarrow0.
\]

For every fixed Fourier window `|k| <= M`,

\[
P_{\le M}u_N\equiv0
\qquad\text{whenever }N>M.
\]

Thus selected-time energy one and integrated enstrophy one-half do not force any fixed finite frequency window to capture positive energy.

The weak temporal trace is equally revealing. In the homogeneous order-minus-one norm,

\[
\|\partial_tu_N(t)\|_{\dot H^{-1}}
=
N e^{-N^2t},
\]

so

\[
\int_0^\infty
\|\partial_tu_N(t)\|_{\dot H^{-1}}\,dt
=
\frac1N\longrightarrow0.
\]

By contrast,

\[
\|\partial_tu_N\|_{L_t^2\dot H_x^{-1}}^2=\frac12.
\]

Therefore even vanishing `L_t^1 H_x^{-1}` temporal variation does not preserve a selected-time `L^2` score under fixed-window or spacetime compactness. A direct `L_t^2H_x^{-1}` trace channel detects the layer only at order one, and the base critical nonlinear budgets do not generically provide a small such channel.

## Claim + counterexample + best salvage

### Killed claim

\[
\boxed{
L_t^\infty L_x^2\text{ selected-time mass}
+
L_t^2\dot H_x^1\text{ bounded action}
+
L_t^1\dot H_x^{-1}\text{ small trace}
\not\Longrightarrow
\text{fixed-window capture}.
}
\]

### Why the dissipation-tax heuristic fails

Frequency `N` costs `N^2` instantaneously but lives for time `N^{-2}`. The integrated enstrophy is therefore independent of `N`. Spatial frequency complexity can escape through shorter temporal residence without paying a growing integrated tax.

This is the parabolic analogue of the endpoint initial-layer obstruction already present in the threshold architecture: a time-supremum score can survive while every spacetime compactness channel disappears.

### Best salvage

The correct replacement must be **time-interior or ancestor-sensitive**. A viable theorem has to force at least one of the following:

1. the selected energy persists for a definite fraction of the parabolic time window;
2. the active high frequency was already present in a backward ancestor and is charged there;
3. a critical nonlinear source regenerates it in the interior and pays a visible supply/flux event;
4. a genuinely time-uniform cap functional detects the initial layer;
5. the observation time is separated from the incoming temporal boundary and a quantitative parabolic smoothing/backward-uniqueness estimate applies.

This motivates the exact next bridge:

## NS-TIME-INTERIOR-FREQUENCY-CAP

For a normalized localized suitable weak solution on a unit parabolic cylinder, prove a dichotomy with constants independent of scale:

\[
\boxed{
\begin{aligned}
&\text{positive selected-time critical energy at an interior time}\\
&\quad\Longrightarrow\quad
\text{fixed-window positive-cone detection}\\
&\qquad\text{or a quantitatively charged backward-ancestor/nonlinear-supply event.}
\end{aligned}}
}
\]

The theorem must explicitly account for pressure, cutoff forcing, local-to-periodic transfer, and the selected-time trace. It cannot be derived from bounded integrated enstrophy alone.

## Consequences for the current proof DAG

1. Yu's clean finite-window positive-cone theorem remains valid in its stated finite-dimensional setting. The obstruction lies in obtaining a scale-uniform active window from localized Navier–Stokes data.
2. The proposed `NS-WINDOW-COMPLEXITY-CHARGED-BY-TAX` theorem is false unless temporal residence or ancestor import is included.
3. Shahmurov's backward-ancestor channel addresses the correct phenomenon conceptually, but the source audit found that this channel is added after the original typed-zero ledger and is not closed by the displayed zero-output definition.
4. Barker–Popkin localization can exploit a controlled interior annulus, but it does not manufacture the required temporal persistence or ancestor charge.
5. The highest-leverage common object is therefore a **parabolic time-frequency cap** coupling spatial window complexity to temporal residence and scale-transition ancestry.

## Lean firewall

The accompanying Lean file formalizes the finite scaling core:

- `parabolicFrequencyAction`: `N^2 * N^{-2} = 1`;
- `parabolicFrequencyWeakTrace`: `N * N^{-2} = N^{-1}`;
- `arbitrarilyHighFrequencyCriticalActionWeakTrace`: above every fixed cutoff and below every positive weak-trace tolerance there exists a frequency with unit parabolic action.

The Lean statements do not formalize the torus, Fourier analysis, or the Navier–Stokes PDE. Those analytic identities are proved directly above. The finite theorems are a kernel-checked firewall for the exact scaling quantifiers.

## Status

No official three-dimensional Navier–Stokes regularity theorem or finite-time blowup construction is obtained. No Millennium alarm condition is met.
