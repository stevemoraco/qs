# Navier–Stokes — Barker–Popkin local Orlicz blow-up as a Dini amplitude-tail theorem

Date: 2026-08-13 UTC  
Primary source: Tobias Barker and Henry Popkin, *Quantitative estimates for the forced Navier–Stokes equations and applications*, arXiv:2602.09951v1 (2026), Theorem 4.2.2.

**Status:** PROVED equivalent distribution-function and dyadic-shell formulations; NOT a regularity proof; FIVE-ALARM OFF.

## 1. Source functional

Barker–Popkin prove that there is a universal `theta in (0,1)` such that at every singular point `(x_*,T_*)` and every `delta>0`,

\[
\limsup_{t\uparrow T_*}
\int_{B_\delta(x_*)}
\Phi(|u(x,t)|)\,dx
=\infty,
\tag{1.1}
\]

where

\[
\Phi(s)=\frac{s^3}{L(s)^\theta}
\]

and `L` is the positive triple-logarithmic factor printed in their theorem.

Choose `S_*` sufficiently large that `L` is increasing and

\[
0\le \theta\frac{sL'(s)}{L(s)}\le1
\qquad(s\ge S_*).
\]

Then

\[
\Phi'(s)
=s^2L(s)^{-\theta}
\left(3-\theta\frac{sL'(s)}{L(s)}\right),
\]

so

\[
\boxed{
2\frac{s^2}{L(s)^\theta}
\le\Phi'(s)
\le3\frac{s^2}{L(s)^\theta}
\qquad(s\ge S_*).
}
\tag{1.2}
\]

## 2. Exact layer-cake form

For a measurable field `f` on a finite-measure set `B`, define

\[
\mu_f(\lambda)=|B\cap\{|f|>\lambda\}|,
\qquad
\eta_f(\lambda)=\lambda^3\mu_f(\lambda).
\]

Tonelli's theorem gives, with extended values allowed,

\[
\int_B[\Phi(|f|)-\Phi(S_*)]_+dx
=
\int_{S_*}^{\infty}\Phi'(\lambda)\mu_f(\lambda)d\lambda.
\tag{2.1}
\]

Using `(1.2)`,

\[
\boxed{
2\int_{S_*}^{\infty}
\frac{\eta_f(\lambda)}{\lambda L(\lambda)^\theta}d\lambda
\le
\int_B[\Phi(|f|)-\Phi(S_*)]_+dx
\le
3\int_{S_*}^{\infty}
\frac{\eta_f(\lambda)}{\lambda L(\lambda)^\theta}d\lambda.
}
\tag{2.2}
\]

### Theorem NS-BP-DINI-1

At every Barker–Popkin singular point and every `delta>0`,

\[
\boxed{
\limsup_{t\uparrow T_*}
\int_{S_*}^{\infty}
\frac{\lambda^3
|B_\delta(x_*)\cap\{|u(t)|>\lambda\}|}
{\lambda L(\lambda)^\theta}
\,d\lambda
=\infty.
}
\tag{2.3}
\]

Thus a singular trajectory must accumulate a non-summable weighted charge across amplitude levels. A merely nonzero weak-`L^3` tail is not the full obstruction.

## 3. Dyadic fresh-amplitude form

For `2^j >= S_*`, define

\[
a_j(f;B)=2^{3j}|B\cap\{|f|>2^j\}|,
\qquad
w_j=L(2^j)^{-\theta}.
\]

Monotonicity of `mu_f` and slow variation of `L` on dyadic intervals give constants `c,C>0` such that

\[
\boxed{
c\sum_{j\ge J+1}w_ja_j(f;B)
\le
\int_{2^J}^{\infty}
\frac{\eta_f(\lambda)}{\lambda L(\lambda)^\theta}d\lambda
\le
C\sum_{j\ge J}w_ja_j(f;B).
}
\tag{3.1}
\]

Equivalently, pass to the disjoint amplitude shells

\[
E_j=\{2^j<|f|\le2^{j+1}\},
\qquad
c_j=2^{3j}|E_j|.
\]

The geometric kernel relating the nested coefficients `a_j` to the fresh shell coefficients `c_j` is summable, so `sum_j w_j a_j < infinity` iff `sum_j w_j c_j < infinity`, up to universal constants after discarding finitely many low levels.

This is the correct additive object for a cross-amplitude packing argument: each point belongs to one fresh amplitude shell, not to every nested superlevel label.

## 4. Structural consequence

The natural state variable for a critical concentration proof is not a packet count but the amplitude-shell sequence

\[
(c_j)_{j\ge J_*},
\qquad
c_j=2^{3j}|\{2^j<|u|\le2^{j+1}\}|.
\]

Barker–Popkin divergence is a slowly weighted `ell^1` failure:

\[
\sum_jw_jc_j=\infty.
\]

Weak-`L^3` control is an `ell^infinity`-type bound on a geometrically smoothed tail of the same sequence. The companion sequence dictionary proves these conditions are incomparable.

The exact PDE gate is dynamic: show that actual Navier–Stokes evolution cannot create infinitely much fresh weighted amplitude charge without paying a finite dissipation/pressure/vorticity budget.

## 5. Hostile scope audit

- The layer-cake and dyadic equivalences are function-space identities.
- They do not provide a finite budget for the Dini charge.
- Nested superlevel sets must not be counted as disjoint fresh charges without the shell conversion.
- The Barker–Popkin theorem supplies unbounded limsup, not temporal persistence.
- No Clay theorem is claimed.

\[
\boxed{\text{FIVE-ALARM OFF.}}
\]
