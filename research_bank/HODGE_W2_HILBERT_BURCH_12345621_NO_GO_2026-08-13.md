# A Hilbert–Burch obstruction for the length-24 type (1,2,3,4,5,6,2,1) on W_2(C)

**Date:** 2026-08-13  
**Status:** GREEN for the stated normally-flat graded type; **not a Hodge-conjecture result**.  
**Scope:** a very general nonhyperelliptic genus-four curve C, its Abel surface
S=W_2(C) in J(C), and a normally-flat embedded multiple structure whose
graded normal algebra has Hilbert function
h=(1,2,3,4,5,6,2,1). The conclusion does not cover other Hilbert functions,
non-normally-flat structures, or graded pieces that fail to be vector bundles.

## 1. Target data

Let x=c_1(Theta) on J(C). On S=C^(2), write
X=[p+C], H=x|_S, and D=3X-H. The standard intersection data are
X^2=1, XH=4, H^2=12, K_S=X+H, so D^2=-3 and DK_S=-1.

Put V=N^*_{S/J(C)}, v=c_1(V)=-K_S, and c=c_2(V). Then
v^2=21, integral_S c=6, and Dv=1.

For the d=23 theta-secant target, a rank-24 graded algebra class E in K_0(S)
must satisfy
i_*c_1(E)=0 and
integral_S(ch_2(E)-c_1(E)K_S/2)=-552.                       (1.1)
For a very general curve the numerical kernel of
i_*:NS(S)_Q -> H^6(J(C),Q) is QD, so write c_1(E)=tD with t rational.

## 2. Intrinsic Hilbert–Burch data

The Hilbert numerator is
(1-z)^2 sum h_j z^j = 1-5z^6+3z^7+z^9.
Thus the fiberwise minimal Hilbert–Burch resolution globalizes to bundles
G,Q,L of ranks 5,3,1.

Use the quotient-line convention
pi:P(V)->S, pi_*O(j)=Sym^j V, put xi=c_1(O(1)), and use
xi^2-v xi+c=0. The sheafified minimal resolution is
0 -> pi^*Q O(-7) + pi^*L O(-9) -> pi^*G O(-6) -> O -> 0.   (2.1)
This uses intrinsic minimal generator and syzygy bundles, not a monomial
normal form.

Write g=c_1(G), q=c_1(Q), l=c_1(L),
G_2=ch_2(G), and Q_2=ch_2(Q). Expanding ch(2.1) and reducing by the
projective-bundle relation gives
g=q+l,                                                        (2.2)
q+3l=24v,                                                     (2.3)
G_2-Q_2-l^2/2+24c=0,                                         (2.4)
Q_2=43v^2+3vl-3l^2/2-31c.                                   (2.5)

## 3. Tautological class and contradiction

Through degree seven the quotient algebra has K-class
E=sum_{j=0}^7 Sym^j V - G tensor (O+V) + Q.                  (3.1)
Equations (2.2)--(2.5) yield
c_1(E)=31v+3l,                                                (3.2)
ch_2(E)=111v^2/2-71c-4vl+3l^2/2.                            (3.3)

Since c_1(E)=tD,
l=(tD-31v)/3. Substitution in (3.3) gives
integral_S ch_2(E)=4971-35t/3-t^2/2.
Using DK_S=-1, the target equation (1.1) becomes
3t^2+67t-33138=0.                                             (3.4)
Its discriminant is 402145, while
634^2=401956 < 402145 < 403225=635^2.
Hence (3.4) has no rational solution.

## Theorem

There is no normally-flat embedded multiple structure supported on W_2(C)
whose graded normal algebra has Hilbert function
(1,2,3,4,5,6,2,1) and whose pushed-forward Chern character is the d=23
theta-secant target.

## Claimant / critic / rebuilder

**Claimant.** This is a genuine moving graded-Hilbert stratum, so fixed
monomial and fixed-orbit arguments alone do not dispose of it.

**Critic.** Intrinsic Hilbert–Burch bundles force the nonsquare quadratic
(3.4). No stability assumption, monomial choice, or splitting of V is used.

**Rebuilder.** Apply the projective-bundle Chern-character elimination to
each allowed Betti stratum. One type is not the whole length-24 punctual
Hilbert scheme, and no normally-flat-to-arbitrary passage is made.

## Provenance and scope

Fiberwise inputs are Hilbert–Burch and the projective-bundle formula.
For graded quotient parameter spaces and Betti strata see A. Iarrobino and
J. Yameogo, *The family G_T of graded quotients of k[x,y] of given Hilbert
function*, arXiv:alg-geom/9709021, and A. Iarrobino, *Betti strata of height
two ideals*, arXiv:math/0407364. The C^(2) intersection data are the
classical Macdonald/Poincare formulas.

This is an independently derived obstruction for one finite stratum. It
proves neither the Hodge conjecture nor the nonexistence of every secant
object. No Lean formalization of this global argument is claimed.
