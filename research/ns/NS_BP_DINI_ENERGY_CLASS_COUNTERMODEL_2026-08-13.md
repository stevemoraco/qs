# Navier–Stokes — Leray energy class does not control the Barker–Popkin Dini charge

Date: 2026-08-13 UTC  
Primary criterion being firewalled: Barker–Popkin, arXiv:2602.09951v1, Theorem 4.2.2.

**Status:** PROVED functional countermodel; NOT a Navier–Stokes solution; FIVE-ALARM OFF.

## 1. Purpose

Write

\[
\Phi(s)=\frac{s^3}{L(s)^\theta},
\qquad 0<\theta<1,
\]

with `L` the Barker–Popkin triple-logarithmic factor. This note disproves the purely functional implication

\[
L_t^\infty L_x^2\cap L_t^2\dot H_x^1
\quad+\quad
\text{slice-wise weak-}L^3\text{ smallness}
\Longrightarrow
\text{bounded local }\int\Phi(|u|).
\]

## 2. Spatial blocks

Choose a nonzero divergence-free field

\[
\psi\in C_c^\infty(B_1;\mathbb R^3)
\]

and constants `c_0,c_1>0` such that

\[
|\{y:|\psi(y)|\ge c_0\}|\ge c_1.
\]

Let

\[
A_n=2^n,
\qquad
\varepsilon_n=n^{-1/2},
\qquad
r_n=\varepsilon_n^{1/3}A_n^{-1}.
\]

Choose centers `x_n` so that the balls `B(x_n,r_n)` are pairwise disjoint in one fixed ball, and define

\[
b_n(x)=A_n\psi\!\left(\frac{x-x_n}{r_n}\right).
\]

Then

\[
\|b_n\|_2^2=C_2\frac{\varepsilon_n}{A_n},
\tag{2.1}
\]

\[
\|\nabla b_n\|_2^2=C_3A_n\varepsilon_n^{1/3},
\tag{2.2}
\]

and `|b_n| >= c_0 A_n` on a set of measure at least `c_1 r_n^3`.

For a finite block `[N,M]`, set

\[
g_{N,M}=\sum_{n=N}^M b_n.
\]

## 3. Weak-`L^3` and energy smallness

For `A_{j-1} <= lambda < A_j`, disjointness gives

\[
\lambda^3|\{|g_{N,M}|>\lambda\}|
\le
C A_j^3\sum_{n=j}^M\varepsilon_nA_n^{-3}
\le C\varepsilon_j
\le C\varepsilon_N.
\]

Hence

\[
\boxed{
\|g_{N,M}\|_{L^{3,\infty}}
\le C\varepsilon_N^{1/3}=CN^{-1/6}.
}
\tag{3.1}
\]

Also

\[
\boxed{
\|g_{N,M}\|_2^2
=C_2\sum_{n=N}^M\frac{\varepsilon_n}{A_n}
\le C2^{-N}N^{-1/2}.
}
\tag{3.2}
\]

Both tend to zero uniformly in `M` as `N -> infinity`.

## 4. Arbitrarily large Barker–Popkin charge

The core lower bound gives

\[
\int\Phi(|g_{N,M}|)dx
\ge
c\sum_{n=N}^M
\frac{\varepsilon_n}{L(c_0A_n)^\theta}.
\tag{4.1}
\]

Because `L(c_0 2^n)^theta` grows more slowly than every positive power of `n`, the infinite series on the right diverges. Choose disjoint integer blocks `[N_k,M_k]`, with `N_k -> infinity`, such that

\[
\int\Phi(|g_k|)dx\ge k,
\qquad
g_k=g_{N_k,M_k}.
\tag{4.2}
\]

Then

\[
\|g_k\|_{L^{3,\infty}}\to0,
\qquad
\|g_k\|_2\to0,
\qquad
\int\Phi(|g_k|)dx\to\infty.
\tag{4.3}
\]

## 5. Time localization with finite total Dirichlet action

Choose pairwise disjoint intervals `I_k` accumulating only at `0` and smooth cutoffs `chi_k in C_c^infinity(I_k)` with `chi_k(t_k)=1`. Put

\[
D_k=\|\nabla g_k\|_2^2<\infty
\]

and choose `|I_k|` so small that

\[
|I_k|D_k\le2^{-k}.
\tag{5.1}
\]

Define

\[
v(x,t)=\sum_{k=1}^\infty\chi_k(t)g_k(x),
\qquad -1<t<0.
\]

The sum is locally finite in time, smooth for `t<0`, divergence-free, and supported in one fixed spatial ball. Because the time supports are disjoint,

\[
\sup_{-1<t<0}\|v(t)\|_2^2<\infty,
\]

and

\[
\int_{-1}^0\|\nabla v(t)\|_2^2dt
\le C\sum_k|I_k|D_k<\infty.
\]

At `t_k`,

\[
\boxed{
\|v(t_k)\|_{L^{3,\infty}}\to0,
\qquad
\|v(t_k)\|_2\to0,
\qquad
\int\Phi(|v(t_k)|)dx\to\infty.
}
\tag{5.2}
\]

## Theorem NS-BP-EC1

There exists a smooth divergence-free field

\[
v\in L_t^\infty L_x^2((-1,0)\times\mathbb R^3)
\cap L_t^2\dot H_x^1((-1,0)\times\mathbb R^3)
\]

with compact spatial support and times `t_k -> 0` satisfying `(5.2)`. Therefore no theorem based only on the standard energy and total Dirichlet budgets, even supplemented by slice-wise weak-`L^3` smallness, can yield the Barker–Popkin local Orlicz bound.

## Scope and rebuilt gate

The field is not asserted to solve Navier–Stokes or satisfy the local energy inequality with a Navier–Stokes pressure. The remaining rigidity must come from the equation, pressure structure, and quantitative temporal propagation.

A viable target must show that fresh amplitude shells either pay disjoint Navier–Stokes flux/dissipation charge, persist for a quantitatively controlled parabolic time, or generate vorticity concentration that can be propagated by a Carleman/no-return theorem.

\[
\boxed{\text{FIVE-ALARM OFF.}}
\]
