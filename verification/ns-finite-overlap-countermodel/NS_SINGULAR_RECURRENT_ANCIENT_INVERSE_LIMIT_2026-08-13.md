# Navier–Stokes singular recurrent ancient inverse-limit reduction

**Date:** 2026-08-12 America/Denver / 2026-08-13 UTC  
**Scope:** conditional reduction of the bounded centered-reservoir singular branch. This is not a regularity proof or a blowup construction.

## Premise

Let `(u,p)` be a suitable weak solution in a backward cylinder centered at a singular point `z_*=(x_*,t_*)`. Fix `0<theta<1` and radii

\[
r_k=\theta^k r_0.
\]

Assume that for all sufficiently large `k`, the centered scale-critical reservoir is bounded:

\[
A(Q_{r_k}(z_*))+C(Q_{r_k}(z_*))+D(Q_{r_k}(z_*))\le K.
\]

The local energy inequality on a fixed parent/child ratio then gives a uniform centered dissipation bound at the child scales:

\[
E(Q_{r_k}(z_*))\le K_E(K,\theta).
\]

Normalize at scale `r_k`:

\[
u^{(k)}(y,s)=r_k u(x_*+r_ky,t_*+r_k^2s),
\]

with the pressure normalized modulo functions of time.

## 1. Compactness is strong enough to preserve singularity

On every fixed inner cylinder, the normalized sequence has uniform

\[
L_t^\infty L_x^2\cap L_t^2H_x^1,
\qquad L_{t,x}^3,
\qquad L_{t,x}^{3/2}\text{ pressure}
\]

bounds. The standard compactness lemma for suitable weak solutions therefore gives, after a subsequence,

\[
u^{(k_j)}\to U
\quad\text{strongly in }L^3_{\rm loc},
\]

and

\[
p^{(k_j)}\rightharpoonup P
\quad\text{weakly in }L^{3/2}_{\rm loc}.
\]

This is exactly the compactness topology used in Albritton–Barker, Lemma 2.2.

Because `z_*` is singular, every normalized packet is unbounded in every backward cylinder centered at the normalized origin. Hence, for every `0<R<1`,

\[
\limsup_{j\to\infty}
\|u^{(k_j)}\|_{L^\infty(Q_R)}=\infty.
\]

The persistence-of-singularities proposition of Albritton–Barker then implies that the limit `U` is singular at `(0,0)`.

Therefore every point of the scale omega-limit set is a singular suitable weak solution germ. This is stronger than merely retaining a positive cubic norm.

## 2. Compact recurrent scale dynamics

Let `X_k` denote the normalized velocity/pressure germ, with pressure taken in the quotient by spatial constants depending on time. Define

\[
T_\theta(U,P)(y,s)
=
\bigl(\theta U(\theta y,\theta^2s),
\theta^2P(\theta y,\theta^2s)\bigr).
\]

Then

\[
X_{k+1}=T_\theta X_k.
\]

Use the Fréchet local topology obtained from strong `L^3(Q_\rho)` convergence for velocity and bounded weak `L^{3/2}(Q_\rho)` convergence for pressure, over a countable sequence `rho\uparrow1`. On the uniformly bounded family this topology is metrizable, the tail is precompact, and `T_theta` is continuous.

The omega-limit set

\[
\Omega=
\bigcap_{m\ge0}\overline{\{X_k:k\ge m\}}
\]

is nonempty and compact. It satisfies

\[
T_\theta\Omega=\Omega.
\]

The reverse inclusion is not automatic for an arbitrary forward orbit; here it follows by compactness of predecessors. If `X_{k_j}\to X\in\Omega`, then a subsequence of `X_{k_j-1}` converges to some `Y\in\Omega`, and continuity gives `T_theta Y=X`.

A nonempty compact surjective dynamical system contains a minimal closed invariant subset. Every point in that minimal set is recurrent. Since every element of `Omega` is singular, one obtains a singular recurrent state `X_*` and integers `n_j\to\infty` such that

\[
T_\theta^{n_j}X_*\to X_*
\]

in the local compactness topology.

No periodicity is inferred.

## 3. Surjective prehistory glues to a global ancient solution

Since `T_theta:Omega->Omega` is surjective, choose a full backward orbit

\[
\ldots,X_{-2},X_{-1},X_0=X_*,
\qquad
T_\theta X_{-m-1}=X_{-m}.
\]

For each `m>=0`, define on the expanding cylinder `Q_{theta^{-m}}`

\[
\mathcal U_m(y,s)
=
\theta^m U_{-m}(\theta^m y,\theta^{2m}s),
\]

and similarly for pressure with factor `theta^{2m}`. The predecessor identity gives exact agreement on overlaps:

\[
\mathcal U_{m+1}|_{Q_{\theta^{-m}}}
=
\mathcal U_m.
\]

After adjusting pressure by time-dependent constants on overlaps, the pairs glue to a global ancient suitable weak solution

\[
(\mathcal U,\mathcal P)
\quad\text{on}\quad
\mathbb R^3\times(-\infty,0).
\]

The pressure gauge adjustment does not change the equation or local energy inequality because `div U=0` and the test functions are spatially compactly supported.

Its restriction to `Q_1` is the singular recurrent state `X_*`, so the ancient solution is singular at the terminal origin.

## 4. Uniform centered critical growth

Every predecessor belongs to the same compact bounded reservoir. Critical scaling therefore gives, on the geometric radii `R_m=theta^{-m}`,

\[
A(Q_{R_m})+C(Q_{R_m})+D(Q_{R_m})+E(Q_{R_m})
\le K_*(K,\theta).
\]

Monotonicity of the integrals and comparability of adjacent geometric radii extend this to every `R>0`:

\[
\boxed{
\sup_{R>0}
\bigl[A(Q_R)+C(Q_R)+D(Q_R)+E(Q_R)\bigr]
<\infty.
}
\]

This is a **centered** global critical growth bound. It must not be silently upgraded to the Albritton–Barker quantity

\[
\mathbf I
=
\sup_{Q'\subset\mathbb R^3\times\mathbb R_-}
[A(Q')+C(Q')+D(Q')+E(Q')],
\]

which takes a supremum over all translated parabolic balls. Translation-uniform control is an additional theorem.

## 5. Backward good slices on expanding balls

The centered cubic bound gives

\[
\int_{-R^2}^0\int_{B_R}|\mathcal U|^3
\le K_*R^2.
\]

Averaging on `[-R^2,-R^2/2]` yields a time `t_R` in that interval with

\[
\boxed{
\int_{B_R}|\mathcal U(x,t_R)|^3\,dx
\le 2K_*.
}
\]

For `R\to\infty`, these are backward times tending to `-infinity` and balls exhausting space. This almost reaches the Albritton–Barker Liouville hypothesis, but not quite: their theorem requires a bound on the **global** `L^3(R^3)` norm at a backward sequence of times. The tail outside `B_R` is uncontrolled.

Thus the exact forbidden upgrade is

\[
\sup_R\|\mathcal U(t_R)\|_{L^3(B_R)}<\infty
\not\Longrightarrow
\sup_R\|\mathcal U(t_R)\|_{L^3(\mathbb R^3)}<\infty.
\]

## 6. Exact next rigidity gates

The bounded-reservoir branch is now reduced to either of two sharp theorems.

### NS-RECURRENT-LERAY-RIGIDITY

No nonzero terminally singular ancient suitable weak solution with the centered critical growth bound above can be recurrent under a fixed parabolic scale shift.

### NS-BACKWARD-L3-TAIL-TIGHTNESS

For such a recurrent ancient solution, the good backward slices can be selected so that

\[
\int_{\mathbb R^3\setminus B_R}
|\mathcal U(x,t_R)|^3\,dx\to0.
\]

Then the global `L^3` norms are uniformly bounded along `t_R\downarrow-\infty`, and the Albritton–Barker Liouville theorem forces `U=0`, contradicting terminal singularity.

The tail theorem is strictly stronger than centered Morrey growth and must use recurrence, pressure compatibility, a no-escape mechanism, or a quantitative concentration-propagation theorem.

## Literature boundary

Albritton and Barker prove:

1. compactness of suitable weak solutions under uniform local `L^3` velocity and `L^{3/2}` pressure bounds;
2. persistence of singularities under that compactness;
3. equivalence between local Type-I singularities, defined using a supremum over all interior parabolic balls, and nontrivial mild bounded ancient solutions with finite Type-I quantity;
4. a Liouville theorem for mild ancient solutions with uniformly bounded global `L^3` norm along backward times tending to `-infinity`.

The reduction above uses the first two results. It does not claim the stronger translated Type-I or global `L^3` hypotheses without proof.

## Status

No official three-dimensional Navier–Stokes existence/smoothness theorem or finite-time blowup construction is obtained. No Millennium alarm condition is met.
