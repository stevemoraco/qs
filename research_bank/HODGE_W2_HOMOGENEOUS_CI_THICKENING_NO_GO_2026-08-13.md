# Hodge target: homogeneous binary complete-intersection W2 thickenings fail at length 24

**Date:** 2026-08-13  
**Status:** GREEN after independent reconstruction of the resultant, K-theory, Chern coefficients, and final discriminant.  
**Millennium status:** narrow nonreduced-architecture obstruction only.

## 1. Setup

Let \(C\) be a very general nonhyperelliptic genus-four curve,
\(A=J(C)\), and
\[
 i:S=W_2(C)\hookrightarrow A.
\]
On \(S\), put
\[
 X=[C+p],\quad H=i^*[\Theta],\quad K=X+H,\quad
 D=3X-H.
\]
Then
\[
 X^2=1,\quad XH=4,\quad H^2=12,\quad
 D^2=-3,\quad DK=-1. \tag{1.1}
\]
Let
\[
 V=N^*_{S/A},\qquad v=c_1(V)=-K,\qquad c_2(V)=6. \tag{1.2}
\]

We study a normally flat thickening \(Z\) of \(S\) whose fiberwise
associated graded algebra is a homogeneous binary complete
intersection
\[
 \operatorname{gr}\mathcal O_Z
 \cong \operatorname{Sym}(V)/(f_a,g_b), \tag{1.3}
\]
with a constant regular-sequence degree type \(a,b\ge2\). Its generic
length is \(ab\). The \(d=23\) theta target requires length 24, hence
\[
 ab=24. \tag{1.4}
\]

The relevant aggregate \(K\)-class on \(S\) is denoted \(E\). The exact
GRR constraints from the companion primitive-multiple note are
\[
 \operatorname{rk}E=24,\qquad c_1(E)=tD+\alpha, \tag{1.5}
\]
where \(t\in\mathbb Z\) and
\(\alpha\in\operatorname{Pic}^0(S)\), and
\[
 \int_S\left(\operatorname{ch}_2(E)
              -\frac12c_1(E)K\right)=-552. \tag{1.6}
\]
Topologically trivial \(\alpha\) does not enter the calculations.

## 2. Relation lines and the resultant identity

Assume \(a\le b\). The minimal degree-\(a\) relation defines a line
bundle \(R\), with \(r=c_1(R)\). The degree-\(b\) generator modulo
\(R\cdot\operatorname{Sym}^{b-a}V\) defines a line bundle \(Q\), with
\(s=c_1(Q)\).

A global lift of the second relation need not exist: on overlaps it
may transform by
\[
 g_i=q_{ij}g_j+h_{ij}f_j.
\]
The resultant is unchanged by \(g\mapsto g+hf\), so it glues and gives
the invariant identity
\[
 R^{\otimes b}\otimes Q^{\otimes a}
 \cong(\det V)^{\otimes ab}. \tag{2.1}
\]
Equivalently,
\[
 br+as=ab\,v. \tag{2.2}
\]
The sign and exponent are checked by the degree-\((1,1)\) case.

The Koszul/Hilbert-series \(K\)-class depends only on \(V,R,Q\), so
the absence of a global lifted \(g\) does not invalidate the following
Chern calculations.

## 3. The three possible degree types

Up to interchange, the factor pairs \(a,b\ge2\) with \(ab=24\) are
\[
 (2,12),\qquad(3,8),\qquad(4,6). \tag{3.1}
\]

### Case (2,12)

The Hilbert-series calculation gives
\[
 c_1(E)=144v-66r-s. \tag{3.2}
\]
Using \(12r+2s=24v\) from (2.2) and
\(c_1(E)=tD\), one obtains
\[
 r=\frac{132v-tD}{60}. \tag{3.3}
\]
Since \(v=-X-H\) and \(D=3X-H\),
\[
 r_X=-\frac{44+t}{20},\qquad
 r_H=\frac{t-132}{60}. \tag{3.4}
\]
Integrality of \(r_X\) requires
\(t\equiv16\pmod{20}\), while integrality of \(r_H\) requires
\(t\equiv12\pmod{60}\). These are incompatible.

### Case (3,8)

Here
\[
 c_1(E)=108v-28r-3s. \tag{3.5}
\]
Together with \(8r+3s=24v\), this gives
\[
 r=\frac{84v-tD}{20}. \tag{3.6}
\]
Thus
\[
 r_X=-\frac{84+3t}{20},\qquad
 r_H=\frac{t-84}{20}. \tag{3.7}
\]
The second coefficient requires \(t\equiv4\pmod{20}\); substituting
this into the first numerator leaves \(16\pmod{20}\), so the first
coefficient is not integral.

### Case (4,6)

Now
\[
 c_1(E)=96v-15r-6s, \tag{3.8}
\]
and the resultant equation is
\[
 3r+2s=12v. \tag{3.9}
\]
Solving with \(c_1(E)=tD\) gives
\[
 r=10v-\frac t6D,\qquad
 s=-9v+\frac t4D. \tag{3.10}
\]
Integrality forces
\[
 t=12n,\qquad n\in\mathbb Z. \tag{3.11}
\]

The degree-two Chern character computed from the Koszul/Hilbert
series is
\[
\begin{aligned}
 \operatorname{ch}_2(E)=\;&242v^2-290c_2(V)-20rv
 -\frac{15}{2}r^2\\
 &-4sv-3s^2. \tag{3.12}
\end{aligned}
\]
Using
\[
 v^2=K^2=21,\quad c_2(V)=6,\quad
 vD=1,\quad D^2=-3,
\]
and including the relative GRR term
\(-c_1(E)K/2=+t/2\), equation (1.6) becomes
\[
 -20955+\frac{124}{3}t+\frac{19}{16}t^2=-552. \tag{3.13}
\]
Substituting \(t=12n\) yields
\[
 171n^2+496n-20403=0. \tag{3.14}
\]
Its discriminant is
\[
 \Delta=14\,201\,668.
\]
But
\[
 3768^2=14\,197\,824
 <\Delta<
 14\,205\,361=3769^2. \tag{3.15}
\]
Thus \(\Delta\) is not a square, and (3.14) has no integral solution.

## 4. The primitive endpoint

The missing factor pair \((1,24)\) is the embedding-dimension-one,
curvilinear/primitive sector. It is excluded independently by the
primitive-multiple theorem:
\[
 (2m-1)u^2-u=4,\qquad m=24,
\]
has no integer solution; more cheaply, the ambient conormal quotient
already gives \(3u^2+u=6\), with nonsquare discriminant 73.

## 5. Theorem and exact frontier

### Theorem 5.1

No normally flat multiplicity-24 thickening of a very general
\(W_2(C)\subset J(C)\) whose associated graded algebra has a constant
homogeneous binary complete-intersection fiber type realizes the
\(d=23\) theta-secant character.

### Surviving constructions

The theorem does **not** cover:

- binary Artin algebras that are not complete intersections, hence
  require at least three Hilbert--Burch relations;
- nonhomogeneous associated graded structures;
- thickenings whose Hilbert function jumps or which are not normally
  flat;
- other reduced supports;
- objects that are complexes rather than pure structure sheaves.

Any survivor must also close the sixteen-class weak-semiregularity
gate in the generalized normal cohomology; Chern matching alone is not
enough.

## 6. Claimant / critic / rebuilder

**Claimant.** Moving from curvilinear algebras to embedding-dimension
two should give enough freedom to meet the target.

**Critic.** At length 24, every homogeneous binary complete
intersection has one of only three nonprimitive degree types. The
resultant determinant identity and the exact GRR moments eliminate all
three.

**Rebuilder.** The next punctual-algebra target is a non-complete-
intersection Hilbert--Burch algebra, a nonhomogeneous deformation, or
a normally nonflat family. Each candidate must be audited at the
actual \(K\)-class and characteristic-action level.

## 7. Scope and provenance

The argument uses the standard Koszul resolution of a homogeneous
binary complete intersection, the invariant binary resultant, and the
Macdonald/Poincare intersection data for \(W_2(C)\). Normal flatness
and constant homogeneous complete-intersection fiber type are
load-bearing hypotheses. This is a research reduction, not a Hodge
class and not a Clay theorem.
