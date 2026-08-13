# Ferrand doubles on \(W_2\) cannot realize the theta-secant slope

**Date:** 2026-08-13  
**Status:** GREEN exact ribbon no-go under the stated very-general Néron–Severi hypothesis. Not a Hodge-conjecture result.

Let \(C\) be a very general nonhyperelliptic genus-four curve,
\[
X=J(C),\qquad S=W_2(C)\cong C^{(2)}\subset X.
\]
Write
\[
\eta=[p+C],\qquad \theta=x|_S.
\]
Macdonald's intersection formulas give
\[
\eta^2=1,\quad
\eta\theta=4,\quad
\theta^2=12,\quad
K_S=\theta+\eta.
\]
For very general \(C\),
\[
\operatorname{NS}(S)=\mathbf Z\theta\oplus\mathbf Z\eta.
\]

## 1. Ferrand double setup

Suppose \(S'\) is an embedded Cohen–Macaulay double structure on \(S\):
\[
0\longrightarrow L
 \longrightarrow\mathcal O_{S'}
 \longrightarrow\mathcal O_S
 \longrightarrow0.
\]
For a multiplicity-two CM rope on smooth \(S\), the nilradical \(L\) is a line bundle, and an embedded Ferrand double requires a surjection
\[
N^*_{S/X}\twoheadrightarrow L.
\]
Let \(M\) be its line-bundle kernel:
\[
0\longrightarrow M
 \longrightarrow N^*_{S/X}
 \longrightarrow L
 \longrightarrow0.
\]
Write
\[
c_1(L)=a\theta+b\eta
\]
modulo \(\operatorname{Pic}^0(S)\), with \(a,b\in\mathbf Z\).

## 2. Complete numerical classification of possible line quotients

Because \(T_X|_S\) is trivial,
\[
c(N_{S/X})=c(T_S)^{-1}.
\]
The invariants of \(C^{(2)}\) give
\[
c_2(N_{S/X})=c_2(N^*_{S/X})=6.
\]
From \(c(N^*)=c(M)c(L)\) and \(c_1(N^*)=-K_S\),
\[
6=(-K_S-c_1(L))c_1(L).
\]
Substituting the intersection table yields
\[
\boxed{
12a^2+8ab+b^2+16a+5b+6=0.
}
\]
Viewed as a quadratic in \(b\), its discriminant must be a square:
\[
n^2=16a^2+16a+1=(4a+2)^2-3.
\]
Thus
\[
(4a+2-n)(4a+2+n)=3.
\]
Checking the four signed factor pairs of \(3\) gives the complete integral solution set
\[
\boxed{
(a,b)\in\{(-1,1),(-1,2),(0,-3),(0,-2)\}.
}
\]
This is only a necessary Chern-class classification; existence of an actual quotient for any listed pair is not asserted.

## 3. Every possible double has the wrong cubic slope

Poincaré/Macdonald gives
\[
\operatorname{ch}(\mathcal O_S)
 =\frac{x^2}{2}-\frac{x^3}{3}+\frac{x^4}{8}.
\]
GRR gives
\[
\operatorname{ch}(i_*L)
 =i_*\left(1+\left(c_1(L)-\frac{K_S}{2}\right)+\cdots\right).
\]
Using
\[
i_*\theta=\frac{x^3}{2},\qquad
i_*\eta=\frac{x^3}{6},
\]
the double satisfies
\[
\operatorname{ch}_2(\mathcal O_{S'})=x^2,
\qquad
\operatorname{ch}_3(\mathcal O_{S'})
 =\frac{3a+b-4}{6}x^3.
\]
For the four numerically possible pairs, the cubic coefficients are
\[
-1,\quad-\frac56,\quad-\frac76,\quad-1.
\]
Each is strictly smaller than the theta-secant slope coefficient
\[
-\frac23.
\]

### Theorem 3.1

No embedded Cohen–Macaulay Ferrand double supported on \(W_2(C)\) has
\[
\frac{\operatorname{ch}_3}{\operatorname{ch}_2}
 =-\frac23x,
\]
the ratio forced by the theta-secant target.

The conclusion holds before the degree-four coefficient is considered.

## 4. The first infinitesimal triple also moves the wrong way

The first infinitesimal neighborhood defined by \(I_S^2\) has associated graded
\[
\mathcal O_S\oplus N^*_{S/X}.
\]
Its low Chern character is
\[
\operatorname{ch}_2=\frac32x^2,\qquad
\operatorname{ch}_3=-\frac53x^3,
\]
with slope
\[
-\frac{10}{9}x,
\]
again strictly more negative than \(-\frac23x\).

Thus both smallest nonreduced repairs—Ferrand doubles and the canonical first infinitesimal triple—move the cubic term in the wrong direction.

## 5. Relation to the primitive-kernel quick test

Put
\[
D=\theta-3\eta.
\]
Then
\[
D\theta=0,\qquad D^2=-3,\qquad DK_S=1.
\]
If one insists that a single double itself preserve the reduced \(W_2\) cubic ratio, GRR forces \(c_1(L)=tD\). The conormal equation becomes
\[
3t^2-t=6,
\]
whose discriminant is \(73\), not a square. This is a quick special-case obstruction; the complete classification above is stronger.

## 6. Claim / critic / salvage

**Claim.** A nonreduced CM structure on \(W_2\) might adjust the top Chern character while retaining the favorable pure codimension-two local algebra.

**Critic.** Every numerically possible Ferrand line quotient makes the cubic slope strictly too negative. The canonical multiplicity-three thickening does the same.

**Salvage.** Higher noncanonical ropes, non-locally-free nilradicals, mixed supports, and genuinely nonsplit higher Hilbert–Burch resolutions remain open. This note addresses multiplicity two and the first infinitesimal triple only.

No Lean verification or Millennium claim is made.
