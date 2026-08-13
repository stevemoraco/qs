# RH odd-Weil certificate execution interface

Date: 2026-08-13 UTC

Status: **exact research interface and obstruction; no RH conclusion;
SIX-ALARM OFF.**

## 1. Purpose

The residual-squared Schur algebra in RH-Lean #992 and qs #310 is now cleanly
replayed, including its residual-visible operator analogue.  This note locates
the first bridge needed to turn that algebra into a certified computation.

The correction is important: finite localized odd-Weil matrix entries are
explicitly definable.  The present non-effectivity begins at the infinite
high-block coercivity theorem and the infinite residual tail, not at the
formal definition of an entry.

## 2. Exact finite matrix

For `a>0`, use the real odd localized basis

```text
s_j(t) = a^(-1/2) sin(pi j t/a) 1_{|t|<=a},   j>=1,
H_jk(a) = W(s_j * ~s_k).
```

Here `~g(x)=conj(g(-x))`; hence `~s_j=-s_j`.  With Suzuki's continuous screw
function `Psi` and `d_j=D s_j=(pi j/a^(3/2))cos(pi j t/a)` on `(-a,a)`, the
one-variable terms in the screw kernel vanish because `integral d_j=0`, and

```text
H_jk(a) = -(pi^2 j k/a^3)
  integral_{-a}^a integral_{-a}^a
    Psi(t-u) cos(pi j u/a) cos(pi k t/a) du dt.
```

Equivalently, set `x=t-u` and integrate `Psi(x)` against the exact elementary
overlap

```text
C_jk(x) = integral_{max(-a,-a-x)}^{min(a,a-x)}
            cos(pi j u/a) cos(pi k(u+x)/a) du.
```

This reduces every entry to one interval integral over `[-2a,2a]`.  Suzuki's
explicit formula for `Psi(|x|)` contains every prime-power term up to
`exp(|x|)` and an archimedean Hurwitz--Lerch term.  Splitting near zero and
using its convergent local expansion gives a direct route to outward-rounded
entry enclosures without an infinite digamma integral.

As a cross-check, direct explicit-formula evaluation uses

```text
hat(s_j)(z) = 2 i (-1)^j pi j sqrt(a) sin(a z)
              / ((a z)^2-pi^2 j^2),
```

with removable values enclosed separately.  Odd parity cancels the
character-level `1/z` tails; the archimedean truncation integrand is
`O(j k log|z|/(a^3 z^4))`, yielding an `O(j k(log R+1)/(a^3 R^3))` tail once
`R>2 pi max(j,k)/a`, after an explicit digamma majorant is proved.

## 3. Residual-penalized certificate

Choose `N<M`.  Let

```text
A   = (H_jk)_{j,k<=N},
B_M = (H_jk)_{N<j<=M,k<=N},
D_M = (H_jk)_{N<j,k<=M}.
```

For an outward-rounded solve `Y`, form

```text
Fhat = A - B_M^*Y - Y^*B_M + Y^*D_M Y,
R_j  = sum_{N<l<=M} H_jl Y_l - H_{j,low},  j>N.
```

A valid infinite certificate requires explicit numbers

```text
D >= mu_L I,       Fhat >= -eta I,
||R|| <= rho,      Delta = eta + rho^2/mu_L.
```

The residual norm includes **all** rows `j>M`.  Given interval matrices and an
analytic omitted-row bound `tau`, one may certify coarsely

```text
Delta <= max(0,-lambda_min(mid(Fhat))+||rad(Fhat)||_op)
       + (||mid(R)||_op+||rad(R)||_op+tau)^2/mu_L.
```

Interval LDL*/Sturm or a rational PSD witness can discharge the finite matrix
inequalities.  They cannot supply `mu_L` or `tau` by themselves.

## 4. Claimant, critic, rebuilder

### Claimant

An effective Yoshida theorem giving `N=N(a0,mu)` uniformly for `0<a<=a0`,
together with an explicit infinite-row residual tail, would make the first
honest `Delta` experiment certificate-executable.  A cofinal family with
`Delta_n->0`, plus the separately stated odd-Weil/RH equivalence and all
operator-domain bridges, is the live target.

### Critic

The quoted Yoshida statement is existential: for every `a0,mu>0`, some `N`
works, but no computable `N(a0,mu)` is supplied.  A positive finite `D_M`
eigenvalue does not lower-bound the infinite high block.  Likewise, checking
only rows through `M` does not bound `R`.  Hidden complement states and
coupling countermodels already show that both substitutions are invalid.

The smallest bad certificate is therefore:

```text
claim: finite D_M positivity and finite residual imply Delta control;
counterexample: add one unseen high direction with negative energy or
                nonzero coupling/residual;
salvage: certify an infinite complement floor and all omitted rows.
```

### Rebuilder

The smallest durable next package is:

1. an interval `H_jk(a)` generator using the one-dimensional `Psi*C_jk`
   integral, with exact prime-power enumeration and explicit series tails;
2. a constructive Yoshida lemma returning `N(a0,mu)` and a proof of the
   infinite high-block lower bound;
3. an explicit square-summable bound for every residual row `j>M`;
4. only then, a small `a,N,M` interval solve reporting `eta,rho,mu_L,Delta`.

Without items 2 and 3, a pilot table is correctly labeled heuristic and is
not a durable RH certificate.

## 5. Repository and source audit

- RH commit `b20ef96eb10f358ec8e75ec345a0487375255797` contains the abstract
  residual-squared certificate but no localized entry generator.
- Existing `weilgram`, Li/zero, `primekl`, `weilsdp`, and `theoremx` artifacts
  use different bases or non-interval assumptions; none instantiates this
  `A/B/D` interface.
- Existing Lean cores formalize finite algebra, not the Weil distribution,
  Suzuki's screw function, constructive Yoshida coercivity, operator closure,
  or the infinite Schur bridge.
- Broughan's older matrix-element treatment and `a=log(sqrt 2)` example
  confirm that finite formulas are classical; the public GRHpack page exposes
  no localized Yoshida interval schedule.

Primary sources:

- Masatoshi Suzuki, arXiv:2206.03682v4:
  https://arxiv.org/pdf/2206.03682
- Hiroyuki Yoshida, *Weil's explicit formula and the Riemann hypothesis*:
  https://projecteuclid.org/journals/advanced-studies-in-pure-mathematics/volume-21/issue-none/Weils-explicit-formula-and-the-Riemann-hypothesis/10.2969/aspm/02110281.pdf
- Kevin Broughan's public GRHpack inventory:
  https://kevinbroughan.nz/grhpack.html

## 6. Bell status

No finite-to-infinite or cofinal arrow is closed here.  This note specifies
exactly what must be computed and exactly which two infinite estimates must be
proved before the computation has RH semantics.

**SIX-ALARM: OFF.  EXECUTION INTERFACE BANKED.**
