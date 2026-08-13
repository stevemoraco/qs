# W2 Jacobian-tangent, Atiyah-trace, and cycle firewall

**Date:** 2026-08-13  
**Status:** exact conditional obstruction plus an explicit countermodel to the
missing support arrow; research only  
**Scope:** deformations of a generically nonreduced Cohen--Macaulay thickening
supported on \(S=W_2(C)\subset J(C)\), where \(C\) is a smooth
nonhyperelliptic curve of genus four  
**Conclusion:** Lombardi--Tirabassi kills transverse deformations only in an
augmented deformation problem that carries a flat embedded lift of the reduced
support.  Perfect-object, module, ideal, cycle, \(K\)-class, and Chern-character
deformations do not by themselves supply that lift.

## 1. Exact geometric input

Let
\[
 A=J(C),\qquad S=W_2(C)\hookrightarrow A ,
\]
with the principal polarization retained.  The tangent space to
\(\mathcal A_4\) has dimension
\[
 \frac{4(4+1)}2=10,
\]
whereas the nonhyperelliptic Jacobian locus has dimension
\[
 3g-3=9.
\]
Thus there are polarized first-order directions \(\kappa\) transverse to the
Jacobian locus.

Lombardi--Tirabassi, arXiv:1410.7986, Theorem 1.4 proves, for a smooth
nonhyperelliptic curve of genus \(g\geq3\) and \(1\leq d<g-1\), that the
forgetful map
\[
 p_{W_d}:\operatorname{Def}_{\iota_d}\longrightarrow
 \operatorname{Def}_{W_d}
\]
is an isomorphism of functors on Artin rings.  Their Corollary 1.5 combines this
with their Theorem 1.1 to give
\[
 \operatorname{Def}_{\iota_d}\simeq\operatorname{Def}_C.
\]
They explicitly conclude that an infinitesimal deformation of a
nonhyperelliptic Jacobian together with \(W_d\) remains along the Jacobian
locus.  The hypotheses apply to \(g=4,d=2\).

This is stronger than a tangent-space dimension count: it is a statement about
the relevant deformation functors.  It is also narrower than a statement about
an arbitrary multiple cycle or a perfect complex.

Primary source:
<https://arxiv.org/abs/1410.7986>, Theorem 1.4 and Corollary 1.5.

## 2. Conditional transverse no-lift theorem

Let \(R=\mathbf C[\epsilon]/(\epsilon^2)\), let \(A_R\) be a polarized
first-order deformation of \(A\) in direction \(\kappa\), and suppose that the
deformation datum includes all of the following:

1. a closed \(R\)-flat subscheme \(Z_R\subset A_R\) specializing to
   \(Z\subset A\);
2. a nilpotent ideal \(\mathcal J_R\subset\mathcal O_{Z_R}\);
3. an \(R\)-flat closed subscheme
   \[
   S_R=\operatorname{Spec}_{Z_R}
       (\mathcal O_{Z_R}/\mathcal J_R)\subset A_R
   \]
   specializing, as an embedded scheme, to \(S=W_2(C)\).

Then \(\kappa\) is tangent to the Jacobian locus.

**Proof.** Forget \(Z_R\) and \(\mathcal J_R\).  The remaining datum is a
deformation of the closed immersion
\[
 \iota_2:S=W_2(C)\hookrightarrow J(C).
\]
Lombardi--Tirabassi Corollary 1.5 says that its ambient ppav direction is a
Jacobian direction.  Hence a transverse \(\kappa\) admits no lift in this
augmented category. \(\square\)

The same conclusion applies whenever a stated equiradical or normal-flat
hypothesis actually includes the flat quotient \(S_R\) above.  Merely saying
“normally flat” without specifying the flat center and its embedded lift is
not enough.

This theorem is bankable but conditional.  It does not assert that a
deformation of \(\mathcal I_Z\), \(\mathcal O_Z\), or a perfect complex
canonically produces \(S_R\).

## 3. The Atiyah--Kodaira--Spencer obstruction stops one arrow earlier

For a perfect complex \(F\) on a smooth ambient variety, Huybrechts--Thomas
identify the obstruction to lifting \(F\) across a square-zero deformation
with the product of its Atiyah class and the Kodaira--Spencer class:
\[
 \operatorname{ob}_F(\kappa)
 =
 (\operatorname{id}_F\otimes\kappa)\circ\operatorname{At}(F)
 \in\operatorname{Ext}^2(F,F).
\]
Under their hypotheses its vanishing is equivalent to the existence of a
perfect-complex lift.  Buchweitz--Flenner give the corresponding module
obstruction and semiregularity construction in terms of powers of the Atiyah
class and trace.

Primary sources:

- Huybrechts--Thomas, arXiv:0805.3527;
- Buchweitz--Flenner, arXiv:math/9912245, especially Sections 3, 4, and 7.

For \(F=\mathcal I_Z\), the logical chain needed by the proposed Schottky
argument is
\[
\begin{aligned}
 \operatorname{ob}_F(\kappa)=0
 &\Longrightarrow \text{perfect or module lift}\\
 &\Longrightarrow \text{flat ideal/algebra lift}\\
 &\Longrightarrow \text{flat embedded reduction }S_R\\
 &\Longrightarrow \kappa\in T\mathcal J_4 .
\end{aligned}
\]
Only the first arrow is supplied by the perfect-object obstruction theory, and
the last arrow is supplied by Lombardi--Tirabassi.  Neither middle arrow follows
from those sources.  Even granting an ideal/algebra lift does not repair the
second middle arrow, as the next section shows.

This does not prove that module lifts can never be promoted to ideals under
additional rank-one or determinant hypotheses.  It says that such a promotion
is an extra theorem, and that promotion alone would still not make the radical
flat.

## 4. Smallest radical-flatness countermodel

Put
\[
 B=\mathbf C[\epsilon]/(\epsilon^2),\qquad
 R_n=B[x]/(x^n-\epsilon),\quad n\geq2.
\]
Because the defining polynomial is monic, \(R_n\) is a free \(B\)-module with
basis
\[
 1,x,\ldots,x^{n-1}.
\]
Thus \(\operatorname{Spec}R_n\to\operatorname{Spec}B\) is finite flat of
degree \(n\).  Its special fiber is
\[
 R_n/\epsilon R_n\simeq\mathbf C[x]/(x^n),
\]
the length-\(n\) thickening of the origin.

As a \(\mathbf C\)-algebra,
\[
 R_n\simeq\mathbf C[x]/(x^{2n}),
 \qquad \epsilon=x^n.
\]
Its nilradical is \((x)\), and the quotient by the total radical is
\[
 R_n/(x)\simeq\mathbf C\simeq B/(\epsilon),
\]
which is not \(B\)-flat.

There is in fact no alternative finite flat rank-one quotient lifting the
reduced point.  Such a quotient would be \(B\), and the image \(a\in B\) of
\(x\) would satisfy \(a^n=\epsilon\).  Write
\(a=a_0+a_1\epsilon\).  If \(a_0=0\), then \(a^n=0\) for \(n\geq2\); if
\(a_0\neq0\), then \(a^n\) has nonzero constant term.  Both contradict
\(a^n=\epsilon\).

The smallest instance is \(n=2\):
\[
 B[x]/(x^2-\epsilon).
\]
The instance \(n=24\) matches the length of the W2 finite-flat algebra target.

### Pure codimension-two CM version

Let \(Y\) be any smooth surface and work in the relative smooth fourfold
\[
 Y\times\mathbf A^2_{x,y}\times\operatorname{Spec}B.
\]
The equations
\[
 y=0,\qquad x^n=\epsilon
\]
define a \(B\)-flat pure codimension-two complete intersection.  Its special
fiber is the \(n\)-fold CM thickening of \(Y\times\{0,0\}\).  Its total
reduction is not \(B\)-flat, and no flat rank-one support quotient exists,
by the same local calculation.

Therefore
\[
 \text{flat CM embedded thickening}
 \not\Longrightarrow
 \text{flat embedded reduction}.
\]
This counterexample is local and does not itself construct an abelian example;
it is decisive against any formal inference based only on flatness, purity,
Cohen--Macaulayness, finite length over the support, or complete-intersection
structure.

## 5. Why Hilbert--Chow and the leading cycle do not restore the support

The family \(x^n=\epsilon\) has special fundamental cycle \(n[0]\), but it is
not \(n\) times a section over \(B\).  For \(n=2\), a repeated section would
give
\[
 (x-a)^2=x^2-2ax+a^2.
\]
Matching \(x^2-\epsilon\) would require \(a=0\) and \(a^2=\epsilon\), which is
impossible.  Equivalently, the Hilbert--Chow image is a deformation of the
multiple zero-cycle, not a choice of one underlying point with multiplicity.

After product with \(Y\), the same statement holds for the leading cycle
\(n[Y]\).  A deformation of \(n[S]\), whether recorded by the fundamental
cycle, Hilbert--Chow, \(K_0\), or the Chern character, does not canonically
divide by \(n\) to produce a flat embedded deformation of \(S\).

Lombardi--Tirabassi concerns the actual minimal subscheme \(W_2\), not merely a
multiple of its cohomology or Chow class.  Hence their theorem cannot be
applied to the multiple-cycle shadow without a separate divisibility or
support-recovery theorem.

## 6. The trace-free firewall

Buchweitz--Flenner's semiregularity components have the form, up to their sign
and indexing conventions,
\[
 \sigma_q(e)=
 \operatorname{Tr}\!\left(
 e\circ\frac{(-\operatorname{At}(F))^q}{q!}
 \right).
\]
Their Atiyah--Chern formula is
\[
 \operatorname{ch}(F)=\operatorname{Tr}\exp(-\operatorname{At}(F)).
\]
Accordingly, applying semiregularity to the characteristic obstruction
\(\operatorname{ob}_F(\kappa)\) records the infinitesimal Hodge variation of
the corresponding Chern-character components.

In the theta target, \(\operatorname{ch}(F)\) is a polynomial in the principal
polarization class.  Along a polarized deformation, that class remains of
type \((1,1)\), so the relevant contractions of \(\kappa\) with all these
polynomial Chern-character components vanish.  Thus the Buchweitz--Flenner
trace shadows of the characteristic obstruction vanish in the polarized
directions under consideration.

The correct conclusion is:
\[
 \sigma(\operatorname{ob}_F(\kappa))=0.
\]
It is not:
\[
 \operatorname{ob}_F(\kappa)=0.
\]
Any surviving obstruction is trace-free.  The Chern character, negative-cyclic
Chern character, \(K\)-class, or fundamental-cycle shadow therefore cannot by
itself recover the missing embedded support deformation.  This is exactly why
the ten-dimensional Hodge kernel can coexist with the nine-dimensional
Jacobian tangent space.

The statement above uses the established identity between the semiregularity
of the characteristic obstruction and infinitesimal Hodge variation.  It
does not claim that every conceivable invariant factors through the
Buchweitz--Flenner trace.

## 7. Claim, counterexample, and best salvage

**Claim that survives.**  If a deformation of the thickening carries a flat
embedded quotient \(S_R\) lifting \(W_2\), then every ambient first-order
direction is tangent to the Jacobian locus.  In particular, no transverse
polarized direction lifts in that augmented category.

**Smallest counterexample to the unconditional bridge.**
\[
 \mathbf C[\epsilon,x]/(\epsilon^2,x^2-\epsilon)
 \simeq\mathbf C[x]/(x^4)
\]
is free of rank two over the dual numbers but has nonflat reduction and no
flat rank-one support quotient.  Its product complete intersection gives the
pure CM codimension-two version.  Replacing \(2\) by \(24\) gives the exact
length relevant to the W2 algebra target.

**Best salvage.**  One must prove one of the following genuinely new bridges:

1. a special rigidity theorem forcing every theta-target algebra deformation
   to be equiradical;
2. a deformation-invariant algebraic structure that extracts a flat
   \(W_2\)-quotient from the particular rank-24 algebra, stronger than its
   \(K\)-class or Chern character;
3. a direct trace-free calculation showing
   \(\operatorname{ob}_{\mathcal I_Z}(\kappa)\neq0\) for some transverse
   \(\kappa\), without trying to reconstruct the reduction.

The third route is the cleanest remaining use of the Schottky direction: pair
the trace-free Atiyah obstruction with an explicit trace-free Ext dual class.
The BF trace maps cannot provide that pairing.

## 8. Exact algebra regression

    # B = C[e]/(e^2), R_n = B[x]/(x^n-e).
    # Monicity gives the B-basis 1,...,x^(n-1).
    # Eliminating e gives C[x]/(x^(2*n)).
    for n in (2, 24):
        # If a=a0+a1*e and a0=0, then a^n=0 for n>=2.
        # If a0!=0, a^n has nonzero constant term.
        # Therefore a^n=e has no solution in B.
        assert n >= 2

No Millennium theorem is proved here.  This note closes a false deformation
arrow and isolates the exact additional theorem needed to exploit the
Jacobian-transverse direction.
