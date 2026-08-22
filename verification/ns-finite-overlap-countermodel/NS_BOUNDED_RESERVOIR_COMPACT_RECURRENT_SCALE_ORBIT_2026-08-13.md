# Navier–Stokes bounded reservoir gives a compact recurrent scale orbit

**Date:** 2026-08-12 America/Denver / 2026-08-13 UTC  
**Scope:** conditional compactness and dynamical reduction for a hypothetical singular scale orbit. This is not a regularity proof or a blowup construction.

## The bounded-reservoir branch

Fix a point `z_*=(x_*,t_*)` and a geometric scale ratio `0<theta<1`. Let

\[
r_k=\theta^k r_0,
\qquad
Q_k=Q_{r_k}(z_*),
\]

and let

\[
A_k,\ E_k,\ C_k,\ D_k
\]

be the standard scale-critical local kinetic-energy, dissipation, cubic-velocity, and pressure quantities. Assume that for all sufficiently large `k`,

\[
C_k+D_k\ge\varepsilon>0
\]

and

\[
A_k+C_k+D_k\le K<\infty.
\]

The first condition is persistent Caffarelli–Kohn–Nirenberg badness. The second is the bounded-reservoir lane isolated in the companion note.

The pressure recurrence and the kernel-checked theorem `cubicEventInEveryAdjacentPair` give constants `delta>0` and `k_0` such that

\[
\boxed{
C_k>\delta\quad\text{or}\quad C_{k+1}>\delta
}
\qquad(k\ge k_0).
\]

Thus cubic events are syndetic: their gaps are at most one scale step.

## Uniform parent-cylinder estimates

Normalize the solution at scale `r_k` by

\[
u^{(k)}(y,s)=r_k u(x_*+r_ky,t_*+r_k^2s),
\]

\[
p^{(k)}(y,s)=r_k^2
\bigl(p(x_*+r_ky,t_*+r_k^2s)-c_k(s)\bigr),
\]

where `c_k(s)` is an arbitrary spatial pressure gauge.

The reservoir bound gives on `Q_1`

\[
\operatorname*{ess\,sup}_{-1<s<0}
\int_{B_1}|u^{(k)}|^2\le K,
\]

\[
\int_{Q_1}|u^{(k)}|^3\le K,
\qquad
\int_{Q_1}|p^{(k)}|^{3/2}\le K.
\]

The local energy inequality at scale `k`, fed from the bounded reservoir at scale `k-1`, gives

\[
\int_{Q_1}|\nabla u^{(k)}|^2
\le K_E(K,\theta)
\]

for all sufficiently large `k`. This is the same parent-to-child Caccioppoli use as in the standard pressure-decay iteration; it does not infer dissipation from `A+C+D` at the same scale without a parent.

Energy-Sobolev interpolation then gives

\[
\|u^{(k)}\|_{L^{10/3}(Q_1)}
\le K_{10/3}(K,\theta).
\]

## Equation-level time compactness

Choose fixed nested cylinders

\[
Q_\rho\Subset Q_{\rho_1}\Subset Q_1,
\qquad 0<\rho<\rho_1<1,
\]

and a spatial cutoff `chi` equal to one on `B_{rho_1}`. The distributional Navier–Stokes equation gives

\[
\partial_s(\chi u^{(k)})
=
\chi\Delta u^{(k)}
-
\chi\nabla\cdot(u^{(k)}\otimes u^{(k)})
-
\chi\nabla p^{(k)}.
\]

After moving derivatives onto test functions, all cutoff terms are controlled by

\[
\nabla u^{(k)}\in L^2,
\qquad
u^{(k)}\otimes u^{(k)}\in L^{3/2},
\qquad
p^{(k)}\in L^{3/2}.
\]

Because the cylinder has finite measure,

\[
\boxed{
\|\partial_s(\chi u^{(k)})\|_
{L_s^{3/2}W_y^{-1,3/2}}
\le K_t(K,\theta,\rho_1).
}
\]

This is the channel that the selected-time initial-layer counterexample lacks at a strength compatible with persistent cubic spacetime mass. It comes from the actual equation and the pressure bound, not from a generic trace assumption.

The Aubin–Lions compactness theorem applied to

\[
H^1(B_1)\Subset L^2(B_1)
\hookrightarrow W^{-1,3/2}(B_1)
\]

therefore gives, after passing to a subsequence,

\[
u^{(k_j)}\to U
\quad\text{strongly in }L^2(Q_\rho).
\]

Interpolating this convergence with the uniform `L^{10/3}` bound yields

\[
\boxed{
u^{(k_j)}\to U
\quad\text{strongly in }L^q(Q_\rho)
\quad\text{for every }2\le q<\frac{10}{3}.}
\]

In particular the convergence is strong in `L^3`.

The pressure sequence is weakly precompact in `L^{3/2}` after the gauge is fixed. Strong `L^3` velocity convergence and weak `L^{3/2}` pressure convergence are enough to pass the distributional equation and all fixed smooth local energy-flux tests, because

\[
u^{(k_j)}\otimes u^{(k_j)}\to U\otimes U
\quad\text{strongly in }L^{3/2},
\]

and

\[
p^{(k_j)}u^{(k_j)}\rightharpoonup PU
\quad\text{in }L^1.
\]

## Fixed finite smooth observation bank

The compactness has an immediate quantitative consequence that is stronger than a fixed spatial Fourier cutoff.

Let `K_comp` be the closure in `L^3(Q_rho)` of all normalized bounded-reservoir child packets, and let

\[
K_\delta
=
\{V\in K_{\rm comp}:\|V\|_{L^3}\ge\delta^{1/3}\}.
\]

This is compact and excludes zero. For each `V in K_delta`, choose a norming dual vector

\[
f_V=\frac{|V|V}{\|V\|_{L^3}^2},
\qquad
\|f_V\|_{L^{3/2}}=1,
\qquad
\langle f_V,V\rangle=\|V\|_{L^3}.
\]

A finite subcover and density of smooth compactly supported functions in `L^{3/2}` give finitely many smooth vector tests

\[
g_1,\dots,g_m\in C_c^\infty(Q_\rho;\mathbb R^3)
\]

and a constant `c_delta>0`, depending only on the bounded-reservoir constants, such that

\[
\boxed{
\max_{1\le i\le m}
\left|\iint_{Q_\rho}g_i\cdot V\right|
\ge c_\delta
\qquad
\text{for every }V\in K_\delta.
}
\]

Hence bounded-reservoir cubic events cannot escape every fixed finite **space-time** observation bank. This removes both pure spatial-frequency escape and parabolic initial-layer escape from the cubic-event lane.

It does not yet prove that one of Yu's defect observers, pressure/flux ledgers, or Shahmurov's typed outputs equals one of these velocity tests. That conversion is a separate theorem.

## Compact scale-shift dynamics

For a fixed geometric ratio, define the scale-shift map

\[
T_\theta(U,P)(y,s)
=
\bigl(\theta U(\theta y,\theta^2s),
\theta^2P(\theta y,\theta^2s)\bigr).
\]

The normalized packets satisfy exactly

\[
X_{k+1}=T_\theta X_k,
\qquad X_k=(u^{(k)},p^{(k)}).
\]

Use the strong `L^3` topology for velocity and the bounded weak `L^{3/2}` topology for the pressure gauge. The parent-cylinder compactness above implies that the tail of `{X_k}` is precompact in this product topology, and `T_theta` is continuous.

Let

\[
\Omega
=
\bigcap_{m\ge0}
\overline{\{X_k:k\ge m\}}
\]

be the omega-limit set. Then `Omega` is nonempty and compact. Moreover,

\[
T_\theta\Omega=\Omega.
\]

The nontrivial inclusion follows by taking convergent subsequences of the predecessors `X_{k_j-1}` of any sequence `X_{k_j}` converging into `Omega`.

The adjacent-pair cubic theorem passes to the limit because the cubic functional is continuous under strong `L^3` convergence:

\[
\boxed{
\max\{C(X),C(T_\theta X)\}\ge\delta
\quad\text{for every }X\in\Omega.
}
\]

Every compact surjective dynamical system has a nonempty minimal closed invariant subset. Every point in such a minimal set is recurrent. Since no point and its successor can both have vanishing cubic norm, there is a recurrent nonzero state `X_*` and integers `n_j\to\infty` such that

\[
T_\theta^{n_j}X_*\to X_*
\]

strongly in local `L^3` for velocity and weakly in local `L^{3/2}` for pressure.

Thus the bounded-reservoir singular branch reduces to a concrete object:

\[
\boxed{
\text{a nonzero, NS-realizable, suitable, locally Morrey-bounded,
recurrent scale orbit.}
}
\]

This is stronger than an arbitrary ancient solution and weaker than an exact discretely self-similar profile.

## Literature boundary

Classical Liouville theorems exclude exact backward self-similar profiles under critical integrability or local-energy hypotheses. More recent work also treats rotated and rotated-discretely-self-similar profiles under Type-I bounds in restricted parameter ranges. Those theorems do not exclude a general nonperiodic recurrent orbit.

Likewise, results on locally asymptotically discretely self-similar blowup assume convergence to a fixed time-periodic similarity profile in a critical class. Topological recurrence alone does not supply a period, a fixed rotation rate, or convergence of the full orbit.

The forbidden upgrade is therefore explicit:

\[
\text{recurrent}
\not\Longrightarrow
\text{periodic or discretely self-similar}.
\]

## Highest-leverage independent gate

The bounded-reservoir lane is now reduced to

\[
\boxed{\texttt{NS-RECURRENT-LERAY-RIGIDITY}.}
\]

Prove that no nonzero recurrent scale orbit with the bounds above can satisfy the suitable local energy inequality and the Navier–Stokes pressure compatibility at every scale.

Equivalent viable forms include:

1. a strict scale-Lyapunov functional whose defect is exactly the dissipation/flux tax and whose localization errors vanish on the compact orbit;
2. a uniform-taxation theorem for Yu's full ledger on this compact recurrent set;
3. a theorem upgrading recurrence to an exact periodic/rotated-periodic similarity profile under the NS equation and the Morrey growth bounds;
4. a recurrent-orbit Carleman no-return theorem.

The first two formulations align directly with the current supply–tax and defect-cascade programs.

## Unbounded-reservoir lane

If `A_k+C_k+D_k` is not bounded, none of the compactness above applies uniformly. That lane is a genuine critical concentration/growth problem and remains the natural target for quantitative concentration propagation and forced localization methods.

## Status

No exact official three-dimensional Navier–Stokes existence/smoothness theorem or finite-time blowup construction is proved. No Millennium alarm condition is met.
