# Navier–Stokes — Barker–Popkin record growth is routed entirely through pressure work

Date: 2026-08-13 UTC  
Primary interface: Barker–Popkin arXiv:2602.09951v1, Theorem 4.2.2; companion notes `NS_BP_ORLICZ_SPIKE_COST_2026-08-13.md` and `NS_BP_RECORD_SPIKE_COLLAPSE_2026-08-13.md`.

**Status:** PROVED entropy identity and pressure-work routing for smooth pre-singular solutions; PROVED superenstrophy payment; NOT a global-regularity theorem; FIVE-ALARM OFF.

## 1. Convex Barker–Popkin entropy

Let

\[
\Phi(s)=\frac{s^3}{L(s)^\theta},\qquad 0<\theta<1,
\]

with `L` the Barker–Popkin triple-logarithmic factor. Direct differentiation shows that `Phi` is increasing and convex for all sufficiently large `s`: the derivatives of the slowly varying factor satisfy

\[
\frac{sL'(s)}{L(s)}\to0,
\qquad
\frac{s^2L''(s)}{L(s)}\to0,
\]

while the leading second derivative of `s^3` is positive.

Choose a smooth increasing convex Young function `psi` such that

\[
\psi(s)=0\quad(0\le s\le S_*),
\qquad
c\Phi(s)\le\psi(s)\le C\Phi(s)\quad(s\ge2S_*),
\tag{1.1}
\]

and

\[
0\le\psi''(s)+\frac{\psi'(s)}s
\lesssim\frac{s}{L(s)^\theta}
\quad(s\ge S_*).
\tag{1.2}
\]

Such a patch changes only a bounded amplitude range. Therefore Barker–Popkin local divergence implies divergence of the global entropy

\[
\mathcal E_\psi(t)=\int_{\mathbb R^3}\psi(|u(x,t)|)dx.
\tag{1.3}
\]

For every `t<T_*` before a first singular time, the solution is smooth and bounded and `u(t) in L^2`, so `(1.3)` is finite.

## 2. Exact entropy identity

Let `(u,p)` be a smooth decaying Navier–Stokes solution and put

\[
G(u)=\psi'(|u|)\frac{u}{|u|},
\]

with `G(0)=0`. Testing

\[
\partial_tu+(u\cdot\nabla)u-\nu\Delta u+\nabla p=0
\]

against `G(u)` gives

\[
\boxed{
\frac{d}{dt}\mathcal E_\psi(t)
+\nu\mathcal D_\psi(t)
=
\int_{\mathbb R^3}p\,\operatorname{div}G(u)dx,
}
\tag{2.1}
\]

where

\[
\mathcal D_\psi
=
\int_{\mathbb R^3}
\left[
\psi''(|u|)|\nabla|u||^2
+
\frac{\psi'(|u|)}{|u|}
\big(|\nabla u|^2-|\nabla|u||^2\big)
\right]dx
\ge0.
\tag{2.2}
\]

The transport term cancels exactly:

\[
\int G(u)\cdot(u\cdot\nabla)u
=
\int u\cdot\nabla\psi(|u|)=0.
\]

Convexity makes the viscous term nonnegative. Consequently, **positive growth of the global Barker–Popkin entropy is caused only by pressure work**.

## 3. Quantitative pressure-work route

Let `K_n=4^nK_0`, and let `[s_n,t_n]` be the disjoint record intervals on which

\[
\mathcal E_\psi(s_n)=K_n/2,
\qquad
\mathcal E_\psi(t_n)=K_n.
\]

Integrating `(2.1)` and using `(2.2)` gives

\[
\boxed{
\int_{s_n}^{t_n}\int_{\mathbb R^3}
 p\,\operatorname{div}G(u)\,dxdt
\ge\frac{K_n}{2}.
}
\tag{3.1}
\]

Thus the previously abstract “fresh pressure/flux alternative” is automatic for global entropy records: every record excursion carries pressure work proportional to its new record level.

Because the record intervals are disjoint and `K_n` grows geometrically, a singularity forces the positive pressure-work contribution across those intervals to be non-summable.

## 4. Superenstrophy payment

Let

\[
D(t)=\|\nabla u(t)\|_2^2.
\]

From `(1.2)`,

\[
|\operatorname{div}G(u)|
\lesssim |u||\nabla u|.
\]

The pressure identity `p=R_iR_j(u_iu_j)`, Calderón–Zygmund boundedness, Sobolev, and Hölder give

\[
\|p\|_3
\lesssim\|u\|_6^2
\lesssim D,
\]

and

\[
\||u||\nabla u|\|_{3/2}
\le\|u\|_6\|\nabla u\|_2
\lesssim D.
\]

Therefore

\[
\left|\int p\,\operatorname{div}G(u)dx\right|
\lesssim D(t)^2.
\tag{4.1}
\]

Combining `(3.1)` and `(4.1)` yields the exact record payment

\[
\boxed{
\int_{s_n}^{t_n}D(t)^2dt
\ge cK_n.
}
\tag{4.2}
\]

### Theorem NS-BP-PER1

Every geometric Barker–Popkin entropy record near a hypothetical first singularity is simultaneously:

1. subdiffusive in duration, by the record-spike collapse theorem;
2. pressure-driven, by `(3.1)`;
3. charged at least `cK_n` in `L_t^2` enstrophy, by `(4.2)`.

The standard Leray energy inequality controls `int D dt`, not `int D^2 dt`, so `(4.2)` is not yet a contradiction.

## 5. Rebuilt highest-leverage gate

The remaining theorem can now be stated without an unspecified ledger:

### `NS-BP-PRESSURE-NO-RETURN`

Show that pairwise disjoint record intervals satisfying

\[
\Delta\mathcal E_\psi\asymp K_n,
\qquad
|I_n|=o(\tau_{\rm nat}(K_n)),
\qquad
\int_{I_n}D^2dt\gtrsim K_n
\]

cannot occur for a suitable Navier–Stokes solution with finite energy, because the corresponding pressure-work/vorticity concentration must either propagate for a parabolic time or pay a Carleson-summable localized forcing charge.

This is aligned with Barker–Popkin's forced localization theorem: their truncation produces a whole-space forced solution, and the pressure-containing localization forcing has improved time regularity. Barker's physical-space concentration propagation is the natural no-return mechanism.

## 6. Hostile scope audit

- The entropy is globally integrated; this removes cutoff flux. Local Barker–Popkin divergence implies global divergence, not conversely.
- The convex patch is comparable only above a fixed threshold, which is sufficient for divergence and records.
- `(4.1)` uses smoothness before the first singular time.
- Divergence of `int D^2` is compatible with a singularity and is not ruled out by the Leray budget.
- No finite pressure-work budget is assumed.
- No Clay theorem is claimed.

\[
\boxed{\text{FIVE-ALARM OFF.}}
\]
