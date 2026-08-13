# Navier–Stokes — exact amplitude-sequence dictionary and incomparability of critical tail classes

Date: 2026-08-13 UTC

**Status:** PROVED function-space dictionary and two countermodels; NOT Navier–Stokes regularity; FIVE-ALARM OFF.

## 1. Dyadic simple fields

Let `(E_j)_{j>=J_0}` be pairwise disjoint measurable subsets of a finite-measure domain `B`, and define

\[
f=\sum_{j\ge J_0}2^j\mathbf1_{E_j},
\qquad
c_j=2^{3j}|E_j|.
\]

Let

\[
w_j=L(2^j)^{-\theta},
\]

where `L` is the Barker–Popkin triple-logarithmic factor.

## 2. Weak `L^3` is an exponentially smoothed `ell^infinity` norm

For `2^{J-1} <= lambda < 2^J`,

\[
\{|f|>\lambda\}=\bigcup_{j\ge J}E_j.
\]

Therefore

\[
\lambda^3|\{|f|>\lambda\}|
\asymp
2^{3J}\sum_{j\ge J}|E_j|
=
\sum_{j\ge J}2^{-3(j-J)}c_j.
\]

Define

\[
(Hc)_J=\sum_{j\ge J}2^{-3(j-J)}c_j.
\]

Then

\[
\boxed{
\|f\|_{L^{3,\infty}}^3\asymp\sup_{J\ge J_0}(Hc)_J.
}
\tag{2.1}
\]

Moreover,

\[
f\in L^{3,\infty}_0
\quad\Longleftrightarrow\quad
(Hc)_J\to0.
\tag{2.2}
\]

For bounded nonnegative sequences `c`, `(2.2)` is equivalent to `c_j -> 0`.

## 3. Barker–Popkin is a weighted `ell^1` norm

For

\[
\Phi(s)=\frac{s^3}{L(s)^\theta},
\]

disjointness gives the exact identity

\[
\boxed{
\int_B\Phi(|f|)dx
=
\sum_{j\ge J_0}w_jc_j.
}
\tag{3.1}
\]

Thus

\[
\boxed{
L^{3,\infty}\text{ tail control}\leftrightarrow \ell^\infty,
\qquad
\text{Barker–Popkin control}\leftrightarrow \ell^1(w).
}
\tag{3.2}
\]

## 4. Countermodel A: vanishing weak tail, infinite Barker–Popkin charge

Take

\[
c_j=j^{-1/2},
\qquad
|E_j|=2^{-3j}j^{-1/2}.
\]

Then `c_j -> 0`, hence `f in L^{3,infinity}_0`. But `w_j` decays more slowly than every negative power of `j`; for large `j`, `w_j >= j^{-1/4}`. Therefore

\[
\sum_jw_jc_j
\ge
\sum_{j\gg1}j^{-3/4}
=\infty.
\]

Hence

\[
\boxed{
f\in L^{3,\infty}_0
\not\Longrightarrow
\int_B\Phi(|f|)<\infty.
}
\tag{4.1}
\]

## 5. Countermodel B: finite Barker–Popkin charge, nonvanishing weak tail

Because `w_j -> 0`, choose a strictly increasing sequence `j_k` such that `w_{j_k} <= 2^{-k}`. Set

\[
c_{j_k}=1,
\qquad
c_j=0\quad(j\notin\{j_k\}),
\]

and `|E_{j_k}|=2^{-3j_k}`. Then

\[
\int_B\Phi(|f|)dx
=
\sum_kw_{j_k}
\le1.
\]

But `(Hc)_{j_k} >= 1` for every `k`, so the weak-`L^3` amplitude tail does not vanish. Therefore

\[
\boxed{
\int_B\Phi(|f|)<\infty
\not\Longrightarrow
f\in L^{3,\infty}_0.
}
\tag{5.1}
\]

## Theorem NS-AMP-SEQ1

On finite-measure domains, the Barker–Popkin local Orlicz class and the vanishing-amplitude-tail subspace `L^{3,infinity}_0` are incomparable.

Consequences:

1. weak-`L^3` precompactness cannot be substituted for Barker–Popkin control;
2. Barker–Popkin finiteness cannot be substituted for a uniform weak-`L^3` tail modulus;
3. a proof using both mechanisms must control both the `ell^infinity` tail and the weighted `ell^1` Dini charge, or prove an equation-specific bridge along actual Navier–Stokes trajectories;
4. the fresh amplitude-shell sequence `c_j` is the smallest common state object on which the two mechanisms can be compared without a topology or quantifier swap.

## Lean decision

The finite form of `(2.1)` and `(3.1)` is a reasonable future Lean target. It was not duplicated in this run because the decisive packing countermodel is already kernel-replayed on `automation/ns-packing-foundation-replay-20260813`, while formalizing finite geometric-sum arithmetic would not reduce the live PDE uncertainty.

\[
\boxed{\text{FIVE-ALARM OFF.}}
\]
