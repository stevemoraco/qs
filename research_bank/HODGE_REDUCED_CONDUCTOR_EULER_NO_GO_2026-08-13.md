# Hodge theta target: reduced-conductor architecture no-go

**Date:** 2026-08-13  
**Status:** GREEN for Theorems 2.1 and 3.1 under their explicit hypotheses; architecture obstruction only.  
**Millennium status:** no Hodge-conjecture proof or disproof. No Lean verification is claimed.

## 1. Target Euler characteristic

Let ((A,Theta)) be a principally polarized complex abelian fourfold, put
(x=c_1(Theta)), and normalize (int_A x^4=4!=24). For
(kge 1), the theta-secant rank-one target with (d=24k-1) forces a
pure codimension-two quotient (Z), if one exists, to satisfy

[
 operatorname{ch}(mathcal O_Z)
 =12k x^2-8k x^3+(-24k^2+4k)x^4 .
]

Consequently

[
 chi(mathcal O_Z)
 =int_A operatorname{ch}_4(mathcal O_Z)
 =96k(1-6k)<0. 	ag{1.1}
]

The following two theorems rule out common reduced gluing
architectures by proving the opposite sign.

## 2. Simple-normal-crossing unions

### Theorem 2.1

Let (Z=igcup_{i=1}^n S_isubset A) be a reduced projective surface.
Assume:

1. each (S_i) is a smooth projective surface (more generally, a
   normal Cohen--Macaulay surface subvariety of (A) for which
   (chi(mathcal O_{S_i})ge0));
2. the union is simple normal crossing;
3. every scheme-theoretic pair intersection
   (C_{ij}=S_icap S_j) is a reduced projective curve; and
4. there are no triple intersections.

Then
[
 chi(mathcal O_Z)ge0.
]
In particular, (Z) cannot have the target character (1.1).

### Proof

The SNC hypotheses give the exact Mayer--Vietoris sequence
[
 0longrightarrowmathcal O_Z
 longrightarrowigoplus_imathcal O_{S_i}
 longrightarrowigoplus_{i<j}mathcal O_{C_{ij}}
 longrightarrow0,
]
and hence
[
 chi(mathcal O_Z)
 =sum_ichi(mathcal O_{S_i})
  -sum_{i<j}chi(mathcal O_{C_{ij}}). 	ag{2.1}
]

For a smooth (S_i), the inclusion (S_i	o A) makes (S_i) a
variety of maximal Albanese dimension. Generic vanishing gives
(chi(omega_{S_i})ge0), and surface Serre duality gives
(chi(mathcal O_{S_i})=chi(omega_{S_i})). For normal
Cohen--Macaulay subvarieties the same sign follows in the stated scope
from Pareschi's generic-vanishing theorem.

It remains to audit the curve sign. An abelian variety contains no
rational curves. Thus every irreducible component of the normalization
(
u:widetilde C	o C_{ij}) has genus at least one. From
[
 0	omathcal O_C	o
u_*mathcal O_{widetilde C}	o Q	o0
]
with (Q) of finite length,
[
 chi(mathcal O_C)
 =sum_a(1-g_a)-operatorname{length}(Q)le0. 	ag{2.2}
]
The argument applies componentwise when (C) is disconnected.
Substituting the component and curve signs in (2.1) proves the claim.
(square)

## 3. Flat double-conductor gluings

### Theorem 3.1

Let (Zsubset A) be a reduced projective surface with normalization
(
u:ar Z	o Z). Assume its conductor square has reduced conductor
curves and the exact structure-sheaf sequence
[
 0	omathcal O_Z	o
 
u_*mathcal O_{ar Z}oplusmathcal O_D
 	o g_*mathcal O_{ar D}	o0. 	ag{3.1}
]
Assume further:

1. (chi(mathcal O_{ar Z})ge0);
2. (Dsubset A) is a smooth projective curve, possibly disconnected;
3. (g:ar D	o D) is a finite flat double cover with (ar D)
   reduced.

Then
[
 chi(mathcal O_Z)ge0.
]
Thus this conductor architecture cannot realize (1.1).

### Proof

In characteristic zero the trace splits
[
 g_*mathcal O_{ar D}cong
 mathcal O_Doplus L^{-1}
]
for a line bundle (L) on (D). The algebra structure is determined
by a nonzero section of (L^{otimes2}); equivalently, on each
component,
[
 L^{otimes2}congmathcal O_D(B)
]
for an effective branch divisor (B). Reducedness excludes the
identically zero multiplication, so (deg L=deg(B)/2ge0).

Riemann--Roch on the smooth curve gives
[
 chi(mathcal O_{ar D})
 =chi(mathcal O_D)+chi(L^{-1})
 =2chi(mathcal O_D)-deg L. 	ag{3.2}
]
Taking Euler characteristics in (3.1) and using (3.2),
[
 chi(mathcal O_Z)
 =chi(mathcal O_{ar Z})
   +chi(mathcal O_D)-chi(mathcal O_{ar D})
 =chi(mathcal O_{ar Z})
   -chi(mathcal O_D)+deg L. 	ag{3.3}
]
As in (2.2), (Dsubset A) has no rational normalization component,
so (chi(mathcal O_D)le0). All three terms on the last line of
(3.3) are therefore nonnegative. (square)

The same proof works for a reduced Gorenstein conductor curve whenever
the trace-free summand is invertible, curve Riemann--Roch applies, and
the branch divisor is effective Cartier. Those conditions are not
suppressed in the theorem.

## 4. Claimant / critic / rebuilder

**Claimant.** The negative Euler characteristic (1.1) might be
obtained by gluing normal maximal-Albanese surfaces along ordinary
reduced double curves.

**Critic.** The SNC formula and the flat double-conductor formula give
the opposite sign. Component Euler characteristics are nonnegative;
reduced curves inside an abelian variety have nonpositive
(chi(mathcal O)); subtracting their contribution only increases
the surface Euler characteristic.

**Rebuilder.** A surviving reduced target must leave at least one of
the proved hypotheses. Concrete escape routes are:

- nonreduced conductor structure;
- a nonflat conductor map or noninvertible trace-free module;
- embedded zero-dimensional conductor corrections;
- triple or higher gluing whose Cech correction is load-bearing;
- nonnormal components outside the cited normal-CM generic-vanishing
  theorem; or
- a genuinely non-SNC codimension-one singular locus.

This dovetails with the independent result that every target has
negative (chi(mathcal O_Z)), hence cannot be normal CM, and that
the remaining reduced CM case has a curve of nonnormality.

## 5. A killed bridge: Du Bois is not rational

A tempting inference is
[
 Z	ext{ Du Bois}quadLongrightarrowquad
 mathcal O_Zsimeq Rf_*mathcal O_Y
]
for an ordinary resolution (f:Y	o Z). This is false: the displayed
property is characteristic of rational singularities, not arbitrary
Du Bois singularities. An irreducible nodal rational curve is Du Bois,
but its normalization is (mathbf P^1); the normalization exact
sequence changes the Euler characteristic. Du Bois theory identifies
(mathcal O_Z) with the degree-zero Du Bois complex obtained from a
hyperresolution, not with the structure sheaf of one ordinary
resolution.

Therefore no claim is made here that arbitrary Du Bois, slc, or
demi-normal subvarieties of abelian varieties have nonnegative
(chi(mathcal O)). Theorems 2.1 and 3.1 use their explicit Cech or
conductor sequences instead.

## 6. Scope and sources

- Giuseppe Pareschi, *Gaussian maps and generic vanishing I:
  subvarieties of abelian varieties*, arXiv:1401.7442, for the
  normal-Cohen--Macaulay generic-vanishing input. The normality
  hypothesis is essential.
- Standard Green--Lazarsfeld generic vanishing for smooth varieties of
  maximal Albanese dimension.
- Standard Ferrand conductor square and trace decomposition for finite
  flat double covers in characteristic not two.
- The target character and its pure-CM reduction are recorded in the
  companion research-bank notes on the theta-secant repair.

This note proves only architecture-specific obstructions. It neither
produces an algebraic Weil class nor proves the Hodge conjecture.
