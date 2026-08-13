# The pure codimension-two Cohen–Macaulay Hodge frontier

**Date:** 2026-08-13  
**Status:** GREEN reductions and no-go theorems; open constructive frontier. Not a Hodge-conjecture result.  
**Scope:** principally polarized abelian fourfolds, target \(v_{24k-1}\), rank-one ideal-sheaf realizations.

## 1. Forced surface character

Let \(X\) be a principally polarized abelian fourfold, \(x=c_1(\Theta)\), and \(d=24k-1\), \(k\ge1\). If
\[
E=I_Z(\Theta)
\]
has
\[
\operatorname{ch}(E)
 =v_d
 =1+x-\frac d2x^2-\frac d6x^3+\frac{d^2}{24}x^4,
\]
then
\[
\boxed{
\operatorname{ch}(\mathcal O_Z)
 =12kx^2-8kx^3+(-24k^2+4k)x^4.
}
\]
Its Hilbert polynomial is
\[
\begin{aligned}
P_Z(m)
 &=\int_X\operatorname{ch}(\mathcal O_Z)e^{mx}\\
 &=144km^2-192km-576k^2+96k\\
 &=48k(3m^2-4m-12k+2),
\end{aligned}
\]
so
\[
\boxed{\chi(\mathcal O_Z)=-96k(6k-1)<0.}
\]

## 2. Why pure CM codimension two is the genuine local escape

Let \(Z\subset X\) be pure Cohen–Macaulay of codimension two, with ideal \(I=I_Z\). Locally, Auslander–Buchsbaum gives
\[
\operatorname{pd}(\mathcal O_Z)=2,\qquad
\operatorname{pd}(I)=1.
\]
Consequently
\[
\mathcal Ext^q(I,I)=0\quad(q\ge2),
\]
and
\[
\mathcal Hom(I,I)=\mathcal O_X,\qquad
\mathcal Ext^1(I,I)=N_{Z/X}:=\mathcal Hom(I,\mathcal O_Z).
\]

Because \(I\) is a perfect rank-one complex, the scalar unit
\[
\mathcal O_X\to R\mathcal Hom(I,I)
\]
is split by the categorical trace, and is an isomorphism on \(H^0\). The cone has the single cohomology sheaf \(N_{Z/X}\) in degree one. Hence
\[
\boxed{
R\mathcal Hom(I,I)\simeq
\mathcal O_X\oplus N_{Z/X}[-1].
}
\]
In particular,
\[
\boxed{
\operatorname{Ext}^2(I,I)
 \cong H^2(\mathcal O_X)\oplus H^1(N_{Z/X}).
}
\]

This is exactly what fails for the transverse nodal and partial-normalization constructions: their ideals have projective dimension two and carry a fatal local \(\mathcal Ext^2\) class. A pure CM ideal removes that local term.

For
\[
HH^2(X)=H^2(\mathcal O_X)\oplus H^1(T_X)\oplus H^0(\Lambda^2T_X),
\]
write an element as \((\beta,\kappa,\pi)\), put
\[
p_\pi=\frac12\iota_\pi(x^2),\qquad q_\kappa=\iota_\kappa x.
\]
Direct contraction of the target character gives, for \(d\ne-1\),
\[
\alpha\cdot v_d=0
\quad\Longleftrightarrow\quad
q_\kappa=0,\qquad \beta=dp_\pi.
\]
Thus the Hodge-character derivative has a 16-dimensional kernel:

- ten polarized primitive directions \(\kappa\) with \(q_\kappa=0\);
- six bivector directions \(\pi\), each compensated by \(\beta=dp_\pi\).

For a pure CM ideal, weak semiregularity reduces to an exact global statement: the corresponding sixteen normal characteristic classes in \(H^1(N_{Z/X})\) must vanish, with no hidden local \(\mathcal Ext^2\) contribution.

## 3. Normal CM surfaces are impossible

If \(Z\) is normal and Cohen–Macaulay, Pareschi's generic-vanishing theorem for normal CM subvarieties of abelian varieties makes \(\omega_Z\) a GV sheaf. Hence
\[
\chi(\omega_Z)\ge0.
\]
Cohen–Macaulay Serre duality in dimension two gives
\[
\chi(\omega_Z)=\chi(\mathcal O_Z),
\]
contradicting
\[
\chi(\mathcal O_Z)=-96k(6k-1)<0.
\]

### Theorem 3.1

No normal Cohen–Macaulay codimension-two subvariety of an abelian fourfold has the forced target character.

**Scope firewall.** Normality is essential in the cited theorem. This does not rule out nonnormal, reducible, or nonreduced CM surfaces.

## 4. Isolated point modifications of transverse unions cannot work

At an ordinary transverse node, let
\[
R=\mathbf C[[u,v,w,z]],\quad
A=R/(u,v),\quad B=R/(w,z),
\]
and let
\[
C=A\times_{\mathbf C}B
\]
be the reduced union ring. Then \(\operatorname{depth}(C)=1\), so \(C\) is not \(S_2\) and not Cohen–Macaulay. Its \(S_2\)-hull is
\[
C^{S_2}=A\oplus B,
\]
with
\[
(C^{S_2})/C\cong\mathbf C
\]
of length one.

Any finite birational two-dimensional Cohen–Macaulay algebra agreeing with \(C\) on the punctured spectrum is \(S_2\), hence equals the \(S_2\)-hull. Since the quotient has length one, the only intermediate finite algebras are \(C\) and \(A\oplus B\), and only the latter is CM.

Therefore a union of smooth surfaces with isolated transverse nodes can become CM by finite-length modification only by fully normalizing every node.

For the \(24k\)-translate \(W_2\) construction, full normalization has
\[
\operatorname{ch}\!\left(\bigoplus_{i=1}^{24k}\mathcal O_{S_i}\right)
 =12kx^2-8kx^3+3kx^4,
\]
not the required
\[
12kx^2-8kx^3+(-24k^2+4k)x^4.
\]

### Theorem 4.1

No choice of partial normalization or other finite-length local modification of the transverse \(W_2\)-union can simultaneously produce the target character and a pure CM surface algebra.

The repair must change the support in positive-dimensional strata or introduce genuinely nonreduced generic structure.

## 5. Rank-two regular zero loci are impossible on Picard-rank one ppav's

Suppose \(Z\) is the regular zero locus of a rank-two vector bundle \(V\) on a generic Picard-rank-one principally polarized abelian fourfold. Write
\[
c_1(V)=a x,\qquad a\in\mathbf Z.
\]
The target gives
\[
[Z]=12kx^2.
\]
For a codimension-two lci surface in an abelian fourfold,
\[
K_Z=\det(V)|_Z,
\]
while the degree-three Chern-character term gives
\[
i_*K_Z=16kx^3.
\]
But adjunction also gives
\[
i_*K_Z=c_1(V)[Z]=12ka x^3.
\]
Therefore
\[
a=\frac43,
\]
contradicting integrality.

### Theorem 5.1

On a Picard-rank-one ppav fourfold, the target cannot be the structure sheaf of a regular rank-two bundle zero locus.

## 6. Split theta-line Hilbert–Burch resolutions are impossible

Assume a minimal split resolution
\[
0\to\bigoplus_{i=1}^{r}L^{-b_i}
 \longrightarrow
 \bigoplus_{j=1}^{r+1}L^{-a_j}
 \longrightarrow I_Z\to0,
\qquad L=\mathcal O_X(\Theta),
\]
and sort
\[
a_1\le\cdots\le a_{r+1},\qquad
b_1\le\cdots\le b_r.
\]
No nonnegativity assumption is needed.

Minimality, codimension at least two, and nonvanishing of every signed maximal minor force
\[
b_i\ge a_{i+1}.
\]
The first Chern class condition gives
\[
\sum_j a_j=\sum_i b_i,
\]
so
\[
a_1=\sum_i(b_i-a_{i+1})\ge0.
\]
Hence all \(a_j,b_i\) are automatically nonnegative.

The padded vector
\[
(0,b_1,\ldots,b_r)
\]
majorizes
\[
(a_1,\ldots,a_{r+1}).
\]
Karamata's inequality for \(t\mapsto t^4\) gives
\[
\sum_i b_i^4\ge\sum_j a_j^4.
\]
But the target \(x^4\)-coefficient requires
\[
\sum_j a_j^4-\sum_i b_i^4
 =24(24k^2-4k)
 =96k(6k-1)>0,
\]
a contradiction.

### Theorem 6.1

No minimal Hilbert–Burch resolution split into arbitrary positive or negative theta powers realizes the target.

This closes the apparent loophole supplied by integral virtual theta-line expressions such as the \(d=23\) coefficient vector \((-3,-19,66,-60,17)\): a virtual \(K\)-class need not be the class of a codimension-two ideal with a minimal split resolution.

## 7. A single semihomogeneous pair is also impossible

Consider a Hilbert–Burch-shaped resolution
\[
0\to E_r\to F_{r+1}\to I_Z\to0
\]
in which both bundles are projectively flat semihomogeneous with a common determinant \(cx\):
\[
\operatorname{ch}(E)=r\exp(cx/r),\qquad
\operatorname{ch}(F)=(r+1)\exp(cx/(r+1)).
\]
The \(x^2\) target equation gives
\[
c^2=24k\,r(r+1).
\]
The \(x^3\) target equation gives
\[
-c=\frac{2r(r+1)}{2r+1}.
\]
Since
\[
\gcd(2r+1,r(r+1))=1,
\]
the integer \(2r+1\) cannot divide \(2r(r+1)\) for \(r\ge1\). Contradiction.

### Theorem 7.1

A single scalar-slope pair of projectively flat semihomogeneous bundles cannot furnish the target Hilbert–Burch resolution.

Mixed-slope and genuinely nonsplit vector bundles remain outside this theorem.

## 8. Rebuilt target

The surviving construction problem is now precise:

> Construct a nonnormal, reducible, or nonreduced **pure Cohen–Macaulay codimension-two** surface \(Z\) with
> \[
> \operatorname{ch}(\mathcal O_Z)
> =12kx^2-8kx^3+(-24k^2+4k)x^4,
> \]
> using a genuinely nonsplit higher Hilbert–Burch resolution, and prove that all sixteen normal characteristic classes in \(H^1(N_{Z/X})\) vanish.

Any proposal based on isolated transverse nodes, normal CM geometry, a rank-two regular section, split theta powers, or one semihomogeneous slope pair is already excluded.

## 9. Provenance and discipline

- Giuseppe Pareschi, *Gaussian maps and generic vanishing I: subvarieties of abelian varieties*, arXiv:1401.7442 / Cambridge 2015, supplies the normal-CM generic-vanishing input. The earlier version arXiv:math/0310026 contained a corrected mistake; normality must not be dropped.
- The remaining arguments use Auslander–Buchsbaum, Hilbert–Burch, trace for perfect rank-one complexes, the \(S_2\)-hull, adjunction, and Karamata.

No Hodge class is constructed, no deformation theorem is closed, and no Lean proof or axiom audit is claimed.
