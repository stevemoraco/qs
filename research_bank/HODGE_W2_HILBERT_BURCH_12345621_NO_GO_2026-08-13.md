# A filtered Hilbert–Burch obstruction for Betti type \((1,2,3,4,5,6,2,1)\) on \(W_2(C)\)

**Date:** 2026-08-13  
**Status:** GREEN for the stated constant minimal-Betti stratum; **not a
Hodge-conjecture result**.

## Scope

Let \(C\) be a very general nonhyperelliptic genus-four curve,
\(S=W_2(C)\subset J(C)\), and let a normally-flat homogeneous embedded
multiple structure have fiber Hilbert function
\[
h=(1,2,3,4,5,6,2,1)
\]
and constant minimal Betti table
\[
\beta_{1,6}=5,\qquad \beta_{2,7}=3,\qquad \beta_{2,9}=1,
\tag{0.1}
\]
with all other minimal Betti numbers zero. The conclusion does not cover
Betti jumping, ghost Betti pairs not visible in the Hilbert numerator,
non-normally-flat structures, or other Hilbert functions.

## 1. Target data

Let \(x=c_1(\Theta)\). On \(S=C^{(2)}\), put
\[
X=[p+C],\quad H=x|_S,\quad D=3X-H.
\]
Then
\[
X^2=1,\quad XH=4,\quad H^2=12,\quad K_S=X+H,
\]
\[
D^2=-3,\quad DK_S=-1.
\]
Put \(V=N^\vee_{S/J(C)}\), \(v=c_1(V)=-K_S\), and \(c=c_2(V)\). Thus
\[
v^2=21,\qquad \int_Sc=6,\qquad Dv=1.
\]
The \(d=23\) theta-secant target forces
\[
i_*c_1(E)=0,\qquad
\int_S\left(\operatorname{ch}_2(E)-\frac12c_1(E)K_S\right)=-552.
\tag{1.1}
\]
For a very general curve the numerical kernel of
\(i_*:\operatorname{NS}(S)_\mathbf Q\to H^6(J(C),\mathbf Q)\) is
\(\mathbf QD\). Write
\[
c_1(E)=tD,\qquad t\in\mathbf Q.
\tag{1.2}
\]

## 2. Filtered relative Hilbert–Burch data

The Hilbert numerator is
\[
(1-z)^2\sum h_jz^j=1-5z^6+3z^7+z^9.
\tag{2.1}
\]
Let \(R=\operatorname{Sym}_S V\) and
\[
B_{i,d}=\operatorname{Tor}^R_i(E,\mathcal O_S)_d.
\]
Under (0.1), constant fiber dimensions and base change make
\[
G=B_{1,6},\quad Q=B_{2,7},\quad L=B_{2,9}
\]
locally free of ranks \(5,3,1\). Local minimal resolutions may glue with
positive-degree off-diagonal terms, so a globally split resolution is not
asserted. The degree filtration has associated graded terms
\[
G\mathcal O(-6),\qquad Q\mathcal O(-7),\qquad L\mathcal O(-9),
\]
and therefore gives the same additive \(K\)-class and Chern character.

Use the quotient-line convention
\[
\pi:\mathbf P(V)\to S,\qquad \pi_*\mathcal O(j)=\operatorname{Sym}^jV,
\]
put \(\xi=c_1(\mathcal O(1))\), and use
\[
\xi^2-v\xi+c=0.
\tag{2.2}
\]
Write
\[
g=c_1(G),\ q=c_1(Q),\ l=c_1(L),\
G_2=\operatorname{ch}_2(G),\ Q_2=\operatorname{ch}_2(Q).
\]
The filtered Hilbert–Burch \(K\)-identity, expanded and reduced using
(2.2), gives
\[
g=q+l,\qquad q+3l=24v,
\tag{2.3}
\]
\[
G_2-Q_2-\frac12l^2+24c=0,
\tag{2.4}
\]
\[
Q_2=43v^2+3vl-\frac32l^2-31c.
\tag{2.5}
\]
Only additivity in \(K_0\) is used; no splitting or monomial normal form is
assumed.

## 3. Tautological class and contradiction

The quotient algebra has the additive \(K\)-class
\[
E=\sum_{j=0}^{7}\operatorname{Sym}^jV
   -G\otimes(\mathcal O\oplus V)+Q.
\tag{3.1}
\]
Equations (2.3)--(2.5) yield
\[
c_1(E)=31v+3l,
\tag{3.2}
\]
\[
\operatorname{ch}_2(E)
 =\frac{111}{2}v^2-71c-4vl+\frac32l^2.
\tag{3.3}
\]
Equation (1.2) forces
\[
l=\frac{tD-31v}{3}.
\]
Substitution in (3.3) gives
\[
\int_S\operatorname{ch}_2(E)
 =4971-\frac{35}{3}t-\frac12t^2.
\]
Using \(DK_S=-1\), (1.1) becomes
\[
3t^2+67t-33138=0.
\tag{3.4}
\]
Its discriminant is
\[
\Delta=402145,
\qquad
634^2=401956<\Delta<403225=635^2.
\]
Thus (3.4) has no rational solution.

## Theorem

No normally-flat homogeneous thickening supported on \(W_2(C)\), lying in
the constant minimal-Betti stratum (0.1), has the \(d=23\) theta-secant
Chern character.

## Claimant / critic / rebuilder

**Claimant.** This is a moving graded-Hilbert stratum, so fixed monomial
and fixed-orbit arguments do not settle it.

**Critic.** A global direct-sum resolution does not follow automatically:
later local generators can mix with polynomial multiples of earlier ones.

**Rebuilder.** Canonical graded Tor sheaves and their degree filtration
retain exactly the additive \(K\)-theory identities used above. The
nonsquare obstruction survives, but the theorem is stated for the constant
minimal-Betti stratum, not merely the Hilbert function.

## Provenance

For graded quotient spaces see A. Iarrobino and J. Yaméogo,
*The family \(G_T\) of graded quotients of \(k[x,y]\) of given Hilbert
function*, arXiv:alg-geom/9709021v2. For Betti strata see A. Iarrobino,
*Betti strata of height two ideals*, arXiv:math/0407364v2. Local freeness
from locally constant fiber dimension over a reduced base is Stacks Project,
Tag 05P1, Lemma 28.21.3; additivity for filtered vector bundles is the
definition of \(K_0\), recorded in Tag 0B37.

This is a finite-stratum obstruction, not a proof of the Hodge conjecture.
The global geometric calculation has not been formalized in Lean.
