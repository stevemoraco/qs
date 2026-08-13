# Hodge target: square-zero and I-adic theta complete-intersection no-go

**Date:** 2026-08-13  
**Status:** GREEN for the displayed calculations after independent hostile correction.  
**Millennium status:** architecture obstruction only; no Hodge-conjecture result.

Let \((A,\Theta)\) be a principally polarized complex abelian fourfold,
put \(x=c_1(\Theta)\), and normalize \(\int_Ax^4=24\). For
\(d=24k-1\), \(k\ge1\), the required pure surface quotient character is

\[
 q_k=12kx^2-8kx^3+(-24k^2+4k)x^4. \tag{1.1}
\]

We rule out two natural nonreduced constructions supported on a smooth
positive theta complete intersection.

## 2. Ferrand square-zero doubles

Let
\[
 S=CI(a\Theta,b\Theta)\subset A,\qquad a,b\in\mathbb Z_{>0},
\]
and write \(H=x|_S\), \(s=a+b\). Suppose \(Z\) is an embedded Ferrand
double of \(S\):
\[
 0\to L\to\mathcal O_Z\to\mathcal O_S\to0, \tag{2.1}
\]
where \(L\) is a line bundle and the embedding is induced by a
surjection
\[
 N^*_{S/A}=\mathcal O_S(-aH)\oplus\mathcal O_S(-bH)\twoheadrightarrow L.
 \tag{2.2}
\]
Put
\[
 P=\int_Sc_1(L)^2,\quad Q=\int_Sc_1(L)H,\quad R=\int_SH^2.
\]

### Theorem 2.1

No such \(Z\) has \(\operatorname{ch}(\mathcal O_Z)=q_k\), for any
\(k\ge1\).

### Proof

The degree-two term forces
\[
 2[S]=12kx^2,\qquad ab=6k,\qquad R=24ab=144k. \tag{2.3}
\]
Grothendieck--Riemann--Roch for the regular embedding gives
\[
 \operatorname{ch}(i_*M)
 =i_*\bigl(\operatorname{ch}(M)\operatorname{td}(N)^{-1}\bigr),
\]
with
\[
 \operatorname{td}(N)^{-1}
 =1-\frac{sH}{2}+\frac{(2s^2-ab)H^2}{12}+\cdots. \tag{2.4}
\]
Applying (2.4) to both summands \(\mathcal O_S\) and \(L\) in (2.1),
the degree-three target equation gives
\[
 Q=24k(6s-8). \tag{2.5}
\]
The degree-four equation, with the quadratic Todd contribution counted
for **both** summands, is
\[
 \frac P2-\frac{sQ}{2}
  +\frac{(2s^2-ab)R}{6}
 =24(-24k^2+4k). \tag{2.6}
\]
Using (2.3)--(2.5), this becomes
\[
 P=48ks^2-192ks+192k-864k^2. \tag{2.7}
\]

On the other hand, (2.2) has a line-bundle kernel. The second Chern
class of \(L(aH)\oplus L(bH)\) therefore vanishes:
\[
 (c_1(L)+aH)(c_1(L)+bH)=0.
\]
After integration,
\[
 P=-sQ-abR
   =-144ks^2+192ks-864k^2. \tag{2.8}
\]
Equating (2.7) and (2.8) gives
\[
 192k(s-1)^2=0. \tag{2.9}
\]
But \(k>0\) and \(s=a+b\ge2\). Contradiction. \(\square\)

### Hostile correction

An earlier draft used one half of the quadratic Todd contribution and
obtained a more complicated Diophantine equation. That was wrong:
both \(\mathcal O_S\) and \(L\) contribute
\((2s^2-ab)H^2/12\). Equation (2.6) is the corrected accounting, and
the obstruction sharpens to the square (2.9).

## 3. Canonical infinitesimal neighborhoods

Let \(I=I_S\) and set \(Z_n=V(I^n)\), \(n\ge1\). The associated graded
algebra is
\[
 \operatorname{gr}\mathcal O_{Z_n}
 =\bigoplus_{j=0}^{n-1}\operatorname{Sym}^jN^*.
\]
Define
\[
 m=\frac{n(n+1)}2,\qquad
 T=\frac{n(n-1)(n+1)}6.
\]
A direct sum over the monomials of
\(\operatorname{Sym}^j(\mathcal O(-aH)\oplus\mathcal O(-bH))\)
gives
\[
 \operatorname{ch}_2(\mathcal O_{Z_n})=mab\,x^2, \tag{3.1}
\]
\[
 \operatorname{ch}_3(\mathcal O_{Z_n})
 =-ab(a+b)\left(\frac m2+T\right)x^3. \tag{3.2}
\]
Thus
\[
 \frac{\operatorname{ch}_3}{\operatorname{ch}_2}
 =-\frac{(a+b)(2n+1)}6. \tag{3.3}
\]
The target ratio from (1.1) is \(-2/3\). Equality would require
\[
 (a+b)(2n+1)=4, \tag{3.4}
\]
impossible for \(a,b,n\ge1\), since the left side is at least six.

### Corollary 3.1

No \(I\)-adic infinitesimal neighborhood \(V(I_S^n)\) of a smooth
positive theta complete-intersection surface realizes even the
degree-two and degree-three parts of the target, for any \(k\).

## 4. Square-zero CM classification in this support class

Suppose a square-zero thickening of the smooth surface \(S\) is
Cohen--Macaulay and has nilradical \(J\):
\[
 0\to J\to\mathcal O_Z\to\mathcal O_S\to0,\qquad J^2=0.
\]
As a maximal Cohen--Macaulay module over the regular surface \(S\),
\(J\) is locally free. Embeddedness supplies a surjection
\(N^*_{S/A}\twoheadrightarrow J\), so \(\operatorname{rank}J\le2\).

- If \(\operatorname{rank}J=1\), this is the Ferrand case excluded by
  Theorem 2.1.
- If \(\operatorname{rank}J=2\), a surjection between rank-two vector
  bundles is an isomorphism. The thickening is the first infinitesimal
  neighborhood \(I^2\), excluded by Corollary 3.1.

Therefore no embedded square-zero Cohen--Macaulay thickening of a
smooth positive theta complete intersection has the target character.

## 5. Claimant / critic / rebuilder

**Claimant.** The negative Euler characteristic missing from reduced
smooth supports might be supplied by a small nilpotent thickening.

**Critic.** The conormal quotient and GRR equations are incompatible
already for a double. The canonical higher \(I\)-adic neighborhoods
miss the required \(x^3/x^2\) slope before their top term matters.

**Rebuilder.** A surviving generically nonreduced target must use a
non-complete-intersection support, a higher nilpotent algebra not
generated by the canonical conormal filtration, or non-locally-free
nilpotent structure outside the square-zero CM setting. It must still
satisfy the weak-semiregularity characteristic-action gate.

## 6. Scope

The theorem is restricted to smooth complete intersections of positive
theta multiples and their embedded square-zero or canonical \(I\)-adic
thickenings. It does not rule out arbitrary ropes, multiple structures
on non-CI supports, or nonsplit higher Hilbert--Burch constructions.
