# Centered critical growth plus exact recurrence does not imply global L3 tails

**Date:** 2026-08-12 America/Denver / 2026-08-13 UTC  
**Scope:** explicit analytic countermodel to a functional-analytic tail upgrade. The field is divergence-free and exactly backward self-similar but is **not** asserted to solve Navier–Stokes. This is not a regularity proof or blowup construction.

## Killed claim

The singular recurrent ancient reduction naturally suggests the implication

\[
\begin{gathered}
\text{uniform centered }A+C+E\text{ growth}\\
+\ \text{exact or recurrent parabolic scaling}\\
+\ \text{local suitable-function-space bounds}
\end{gathered}
\quad\Longrightarrow\quad
\text{global }L^3\text{ control on backward slices}.
\]

This implication is false without using the Navier–Stokes equation and pressure compatibility.

## Explicit divergence-free profile

Fix a nonzero constant vector `a in R^3` and define

\[
V(y)=\frac{a\times y}{1+|y|^2}.
\]

Let `f(r)=(1+r^2)^{-1}`. Since

\[
\nabla f(|y|)\parallel y,
\qquad
(a\times y)\cdot y=0,
\qquad
\nabla\cdot(a\times y)=0,
\]

we have

\[
\nabla\cdot V=0.
\]

The profile is smooth, behaves like `O(|y|)` near the origin, and has the critical tail

\[
|V(y)|\asymp\frac{\sin\angle(a,y)}{|y|}
\qquad(|y|\to\infty).
\]

Consequently,

\[
\int_{B_L}|V|^2\,dy\lesssim L,
\]

\[
\int_{B_L}|V|^3\,dy\lesssim 1+\log(1+L),
\]

and

\[
\int_{\mathbb R^3}|\nabla V|^2\,dy<\infty.
\]

The logarithmic upper bound for the cubic integral is sharp: on any fixed angular sector where `|a cross y| >= c|a||y|`,

\[
\int_{B_L}|V|^3\,dy\gtrsim\log L.
\]

Hence

\[
\boxed{V\notin L^3(\mathbb R^3).}
\]

## Backward self-similar ancient field

For `t<0`, set `tau=-t` and define

\[
U(x,t)=\tau^{-1/2}V\!\left(\frac{x}{\sqrt\tau}\right).
\]

For every `lambda>0`,

\[
\lambda U(\lambda x,\lambda^2t)=U(x,t).
\]

Thus the field is continuously backward self-similar and, in particular, exactly recurrent under every fixed parabolic scale shift.

It remains divergence-free.

## Uniform centered A bound

Changing variables `y=x/sqrt(tau)` gives

\[
\int_{B_R}|U(x,-\tau)|^2\,dx
=
\tau^{1/2}
\int_{B_{R/\sqrt\tau}}|V(y)|^2\,dy
\lesssim R.
\]

Therefore

\[
\boxed{
\sup_{R>0}\operatorname*{ess\,sup}_{-R^2<t<0}
\frac1R\int_{B_R}|U(x,t)|^2\,dx<\infty.
}
\]

## Uniform centered C bound

At one time,

\[
\int_{B_R}|U(x,-\tau)|^3\,dx
=
\int_{B_{R/\sqrt\tau}}|V(y)|^3\,dy
\lesssim
1+\log\left(1+\frac R{\sqrt\tau}\right).
\]

Hence

\[
\begin{aligned}
\frac1{R^2}
\int_{-R^2}^0\int_{B_R}|U|^3
&\lesssim
\frac1{R^2}
\int_0^{R^2}
\left[1+\log\left(1+\frac R{\sqrt\tau}\right)\right]d\tau\\
&=
\int_0^1
\left[1+\log\left(1+s^{-1/2}\right)\right]ds\\
&<\infty.
\end{aligned}
\]

Therefore

\[
\boxed{
\sup_{R>0}C(Q_R)<\infty.
}
\]

## Uniform centered E bound

Since

\[
\nabla_xU(x,-\tau)
=
\tau^{-1}\nabla V(x/\sqrt\tau),
\]

we have

\[
\int_{B_R}|\nabla U(x,-\tau)|^2\,dx
=
\tau^{-1/2}
\int_{B_{R/\sqrt\tau}}|\nabla V|^2\,dy
\lesssim\tau^{-1/2}.
\]

Thus

\[
\boxed{
\sup_{R>0}
\frac1R\int_{-R^2}^0\int_{B_R}|\nabla U|^2<\infty.
}
\]

In particular, on every finite cylinder,

\[
U\in L_t^\infty L_x^2\cap L_t^2H_x^1\cap L_{t,x}^3.
\]

These are the local velocity spaces used for suitable weak solutions.

## Global L3 fails at every backward time

Spatial `L^3` is invariant under the above scaling:

\[
\int_{\mathbb R^3}|U(x,t)|^3\,dx
=
\int_{\mathbb R^3}|V(y)|^3\,dy
=\infty
\]

for every `t<0`.

Moreover, for times `t_R=-cR^2` with fixed `c in (0,1)`, the interior norm is uniformly bounded,

\[
\int_{B_R}|U(x,t_R)|^3dx
=
\int_{B_{1/\sqrt c}}|V|^3dy<\infty,
\]

while the exterior tail is infinite:

\[
\int_{\mathbb R^3\setminus B_R}|U(x,t_R)|^3dx=\infty.
\]

This exactly matches the gap in the recurrent ancient reduction.

## Why this is not a Navier–Stokes counterexample

The field was chosen to isolate scaling, compactness, divergence-free structure, and critical growth. It is not claimed to satisfy

\[
\partial_tU-\Delta U+U\cdot\nabla U+\nabla P=0
\]

for any pressure. In general its Leray-profile residual is nonzero.

Therefore the example does not contradict Navier–Stokes regularity and does not produce a suitable weak solution. Its role is logical:

\[
\boxed{
\text{centered critical bounds + exact recurrence + local energy spaces}
\not\Longrightarrow
\text{global backward }L^3\text{ tails}.
}
\]

## Best salvage

Any proof of `NS-BACKWARD-L3-TAIL-TIGHTNESS` must use an equation-specific mechanism absent from this field. Viable inputs include:

1. pressure compatibility plus a quantitative far-field cancellation;
2. a localized energy/flux identity that charges every persistent `1/|x|` tail;
3. a no-escape theorem from concentration propagation;
4. mildness and translated Type-I control, not merely centered control;
5. a Liouville theorem stated directly for recurrent ancient suitable solutions with centered critical growth.

The countermodel also shows why merely strengthening compactness of the local normalized orbit cannot close the problem: the obstruction lives entirely in the spatial tail outside every normalized compact set.

## Updated minimum cut

The bounded-reservoir lane is reduced to an equation-level theorem:

\[
\boxed{
\texttt{NS-RECURRENT-TAIL-FLUX-RIGIDITY}
}
\]

A nonzero terminally singular recurrent ancient Navier–Stokes solution with uniform centered `A+C+D+E` growth must either generate a quantitatively nonzero far-field pressure/energy flux on infinitely many scales or possess global `L^3`-tight backward slices. The second alternative is killed by the Albritton–Barker Liouville theorem; the first must be taxed by a finite ledger or contradicted by recurrence.

## Status

No official three-dimensional Navier–Stokes existence/smoothness theorem or finite-time blowup construction is obtained. No Millennium alarm condition is met.
