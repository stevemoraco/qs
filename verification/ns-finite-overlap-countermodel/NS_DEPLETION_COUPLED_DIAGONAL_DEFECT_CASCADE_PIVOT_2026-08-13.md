# Navier–Stokes depletion-coupled diagonal and defect-cascade pivot

**Date:** 2026-08-12 America/Denver / 2026-08-13 UTC  
**Scope:** exact finite budget theorem, source synthesis, and next analytic gate. This is not a Navier–Stokes regularity proof or blowup construction.

## Corrected verdict on the vanishing-threshold diagonal

A threshold sequence `tau_k -> 0` cannot repair the first-threshold architecture by parameter choice alone. Bounded total ledger mass, bounded overlap at each fixed scale, and even an absolutely continuous bounded density permit arbitrarily many funded scales as the funding floor tends to zero.

There is, however, one mathematically valid resurrection that is stronger than threshold tuning: prove a **uniform selected-interval depletion theorem** on the exact extraction sequence.

Let `B_k >= 0` be a finite scale-critical budget, `a_k >= 0` the visible activity selected at step `k`, `e_k >= 0` the paid error, and `c > 0` a constant independent of scale and threshold. Assume

\[
B_{k+1}+c a_k\le B_k+e_k.
\]

Then every finite prefix satisfies

\[
\boxed{
 c\sum_{k<N}a_k
 \le
 B_0+\sum_{k<N}e_k.
}
\]

If the event selected at threshold `tau_k` satisfies a quantitative floor

\[
a_k\ge \phi(\tau_k),
\]

if `sum e_k < infinity`, and if the threshold schedule is chosen so that

\[
\sum_k\phi(\tau_k)=\infty,
\]

then visible events cannot occur at every selected step. For a power floor

\[
\phi(\tau)=\tau^q,
\]

one may take

\[
\tau_k=(k+2)^{-1/q},
\]

so `tau_k -> 0` while `sum tau_k^q` diverges.

This is the exact distinction:

\[
\boxed{
\begin{aligned}
&\text{parameter-only vanishing threshold: false;}\\
&\text{depletion-coupled diagonal with a divergent floor sum: viable conditionally.}
\end{aligned}}
\]

The condition is not cosmetic. The coefficient `c`, the activity lower bound, and the error budget must all be uniform on the same selected intervals. A one-step estimate on all dyadic intervals does not automatically restrict to a sparse, solution-dependent extraction.

## Lean finite core

The accompanying Lean file contains two reusable finite theorems:

- `finiteSelectedIntervalDepletion`: exact telescoping of the selected-interval budget inequality;
- `finiteDepletionOverrunImpossible`: a finite-prefix contradiction once the cumulative threshold floors exceed the initial budget plus cumulative errors.

These theorems formalize only the scalar budget algebra. They do not construct the Navier–Stokes budget, prove a PDE depletion estimate, justify a threshold activity floor, or pass from finite prefixes to an infinite extraction.

## Alignment with Runlong Yu's current defect-cascade framework

Runlong Yu's arXiv:2606.12756 (submitted 2026-06-10) gives a conditional reduction near a potential singular point. In its selected-chain formulation, persistent failure of Caffarelli–Kohn–Nirenberg smallness is reduced to either failure of moving-window observability or an NS-realizable cleaned scale-critical defect cascade invisible to combined active-pressure, flux, energy, and adjoint-trace tests.

The source explicitly isolates observable depletion on the selected extraction and warns that sparse extraction needs its own argument. Its divergence condition is therefore the analytic counterpart of the finite Lean theorem above. This supplies a principled rebuild of the Shahmurov cross-scale step:

1. replace fixed-scale overlap bookkeeping by selected-interval budget depletion;
2. use a threshold sequence whose quantitative event floors have divergent sum;
3. conclude that infinitely persistent visible events are incompatible with finite budget and summable errors;
4. reduce the survivor to a genuinely combined-invisible, NS-realizable defect cascade;
5. exclude that survivor or prove effective moving-window observability, thereby obtaining a CKN scale.

The remaining object is not an abstract zero-output profile. It is a **scale-transition defect package constrained simultaneously by Navier–Stokes realizability, pressure compatibility, local energy flux, recurrence, and all observation channels**.

## Why this does not repair the printed typed-zero endpoint

Even a successful depletion theorem would not validate every inference in arXiv:2606.07869v1. The source audit separately found:

- the original typed ledger omits the later backward-ancestor channel `A_anc` used in `L_ext`;
- the displayed first-threshold predicate does not supply the larger low parent later used for seeding;
- score smallness does not by itself imply the separate small spacetime-mass seed;
- the displayed strict contraction theorem invokes a quantitative energy seed absent from its stated hypotheses;
- endpoint score can survive weak/spacetime disappearance through initial-layer or time-spike concentration unless an appropriate cap/trace channel is proved;
- a spatial-only dilation competitor does not remain on the heat/Navier–Stokes solution manifold.

Thus the best salvage is to bypass the unsupported exact-zero endpoint contraction. The repaired route should terminate directly at a CKN scale through depletion and defect exclusion.

## Exact analytic gate

The highest-leverage theorem is now:

### NS-SELECTED-INTERVAL-DEPLETION

For every selected visible event in the actual Navier–Stokes extraction, construct nonnegative scale-critical quantities `B_k`, `a_k`, and `e_k` and constants `c,q>0`, independent of scale and threshold, such that

\[
B_{k+1}+c a_k\le B_k+e_k,
\qquad
a_k\ge c_0\tau_k^q,
\qquad
\sum_k e_k<\infty.
\]

The estimates must hold on the same solution-dependent selected intervals, not merely on all adjacent dyadic steps before extraction.

If this theorem is obtained, choose `tau_k` so that `tau_k -> 0` and `sum tau_k^q = infinity`. The finite theorem forces eventual invisibility. The last obstruction becomes:

### NS-COMBINED-INVISIBLE-EXCLUSION

No nonzero NS-realizable cleaned scale-critical defect cascade can be simultaneously invisible to the active-pressure, flux, local-energy, adjoint-trace, and moving-window tests while satisfying the compatibility and recurrence constraints inherited from a suitable weak solution.

Either theorem would materially reduce the official proof DAG; neither is presently proved here.

## Barker–Popkin localization: exact use and exact missing bridge

Barker and Popkin's arXiv:2602.09951 (submitted 2026-02-10) proves quantitative estimates for critically bounded forced Navier–Stokes solutions and uses them to localize a slightly supercritical Orlicz criterion. Their divergence-free truncation introduces a forcing term in

\[
L_t^2 H_x^1\cap L_{t,x}^6.
\]

For one fixed smooth annulus, the force is finite; under a blowup rescaling

\[
F_\lambda(x,t)=\lambda^3F(\lambda x,\lambda^2t),
\]

its relevant norms scale subcritically and vanish as `lambda -> 0`:

\[
\|F_\lambda\|_{L^2_{t,x}}=\lambda^{1/2}\|F\|_{L^2_{t,x}},
\quad
\|\nabla F_\lambda\|_{L^2_{t,x}}=\lambda^{3/2}\|\nabla F\|_{L^2_{t,x}},
\quad
\|F_\lambda\|_{L^6_{t,x}}=\lambda^{13/6}\|F\|_{L^6_{t,x}}.
\]

This is useful for localizing one fixed solution before rescaling. It does not automatically produce a uniformly controlled force for an arbitrary varying critical sequence. A packet

\[
u_n(x,t)=n\,\chi(n^2(t-t_0))\,\phi(n(x-x_0))
\]

has scale-invariant `L_t^infinity L_x^3` size but can make cutoff-gradient pieces of the localization force grow in the required strong norms. The missing bridge is therefore uniform annular regularity/tightness on the sequence, not the formal existence of a cutoff.

This makes Barker–Popkin complementary to the defect-cascade route: first use scale-transition depletion or concentration compactness to obtain a controlled annulus; then use quantitative forced localization and Carleman propagation.

## Current dependency minimum cut

The first-threshold route has not been repaired. Its minimum cut is now the conjunction of:

1. ancestor-ledger closure;
2. threshold-to-spacetime seed conversion at the correct scale;
3. an explicitly seeded same-scale estimate, or a bypass of that endpoint contraction;
4. selected-interval depletion with threshold-uniform constants;
5. exclusion of the NS-realizable combined-invisible cascade.

The fourth item supplies the only credible vanishing-threshold diagonal. The fifth is the strongest independent rigidity target.

## Status

No official three-dimensional Navier–Stokes existence/smoothness theorem or valid blowup construction is obtained. No Millennium alarm condition is met.
