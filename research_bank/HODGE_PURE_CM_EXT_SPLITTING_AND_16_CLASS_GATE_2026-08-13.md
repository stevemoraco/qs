# Hodge pure-CM local-to-global Ext splitting and exact semiregularity gate

**Date:** 2026-08-13  
**Status:** GREEN derived-category reduction under the stated perfect rank-one hypotheses.  
**Millennium status:** no Hodge-conjecture result.

## 1. Rank-one local-to-global splitting

### Theorem 1.1

Let \(X\) be smooth and let \(I\) be a perfect rank-one coherent ideal
sheaf of projective dimension one. Assume
\(\mathcal Hom(I,I)\cong\mathcal O_X\), and put
\[
 \mathcal N_I:=\mathcal Ext^1(I,I).
\]
Then
\[
 R\mathcal Hom(I,I)\simeq
 \mathcal O_X\oplus\mathcal N_I[-1], \tag{1.1}
\]
and in particular
\[
 \operatorname{Ext}^2(I,I)
 \cong H^2(X,\mathcal O_X)\oplus H^1(X,\mathcal N_I). \tag{1.2}
\]

### Proof

The unit
\[
 u:\mathcal O_X\longrightarrow R\mathcal Hom(I,I)
\]
is split by the perfect-complex trace. Since \(I\) has rank one,
\(\operatorname{tr}\circ u=1\). The projective-dimension-one
hypothesis gives \(\mathcal Ext^q(I,I)=0\) for \(q\ge2\), while the
assumption on endomorphisms says that \(H^0(u)\) is an isomorphism.
Consequently the cone of \(u\) has the single cohomology sheaf
\(\mathcal N_I\) in degree one. The trace splitting identifies the
cone summand and proves (1.1). Taking hypercohomology in degree two
gives (1.2). There is therefore no hidden local-to-global differential
or extension in this rank-one perfect setting. \(\square\)

For a pure codimension-two Cohen--Macaulay ideal \(I=I_Z\) on a smooth
variety, Auslander--Buchsbaum gives projective dimension one. In the
regular-embedding case,
\[
 \mathcal N_I\cong\mathcal Hom(I,\mathcal O_Z)
 \cong N_{Z/X}.
\]
For a non-lci CM ideal, \(\mathcal N_I\) is the generalized normal
sheaf and must not silently be replaced by an ordinary vector bundle.

## 2. The exact sixteen-dimensional Hodge-action kernel

Let \(A\) be a principally polarized abelian fourfold, \(x=[\Theta]\),
and
\[
 v_d=1+x-\frac d2x^2-\frac d6x^3+\frac{d^2}{24}x^4.
\]
Under HKR,
\[
 HH^2(A)=H^2(\mathcal O_A)\oplus H^1(T_A)
          \oplus H^0(\Lambda^2T_A).
\]
Write an element as \((\beta,\kappa,\pi)\), and abbreviate
\[
 p_\pi=\frac12\iota_\pi(x^2),\qquad
 q_\kappa=\iota_\kappa x.
\]
Expanding wedge and contraction on \(v_d\), the vanishing of the Hodge
action is equivalent, degree by degree, to
\[
 \beta+q_\kappa-dp_\pi=0, \tag{2.1}
\]
\[
 \beta-dq_\kappa-dp_\pi=0, \tag{2.2}
\]
\[
 -d\beta-dq_\kappa+d^2p_\pi=0. \tag{2.3}
\]
For \(d\ne-1\), these reduce exactly to
\[
 q_\kappa=0,\qquad \beta=dp_\pi. \tag{2.4}
\]

The kernel therefore has dimension sixteen:

- ten polarized directions
  \[
    \kappa\in\ker\bigl(H^1(T_A)\xrightarrow{\ \iota_{(-)}x\ }
                              H^2(\mathcal O_A)\bigr);
  \]
- six arbitrary bivectors
  \(\pi\in H^0(\Lambda^2T_A)\), with compensating
  \(\beta=dp_\pi\).

All sign conventions may be changed coherently; the kernel statement
is invariant after applying the corresponding global sign change.

## 3. Exact remaining weak-semiregularity gate

Let \(I_Z(\Theta)\) be a rank-one pure-CM candidate with
\(\operatorname{ch}=v_d\), and assume the hypotheses of Theorem 1.1.
The semiregularity square says
\[
 \sigma_I(\operatorname{ev}_I(\alpha))
 =\alpha\cdot\operatorname{ch}(I_Z(\Theta)). \tag{3.1}
\]
Using (1.2), write
\[
 \operatorname{ev}_I(\alpha)
 =\bigl(e_{\rm tr}(\alpha),e_{\rm nor}(\alpha)\bigr)
 \in H^2(\mathcal O_A)\oplus H^1(\mathcal N_I). \tag{3.2}
\]

For weak semiregularity on the evaluated image, the exact kernel
identity is
\[
 \ker(\operatorname{ev}_I)
 =
 \ker\bigl(\alpha\mapsto\alpha\cdot v_d\bigr). \tag{3.3}
\]
In particular, every one of the sixteen classes in (2.4) must have
zero generalized-normal component:
\[
 e_{\rm nor}(\kappa)=0
 \quad(q_\kappa=0), \tag{3.4}
\]
\[
 e_{\rm nor}(dp_\pi,0,\pi)=0
 \quad(\pi\in H^0(\Lambda^2T_A)). \tag{3.5}
\]
The trace component must also vanish on the same classes for the full
kernel equality, but the local-to-global theorem isolates the
load-bearing trace-free debt in \(H^1(\mathcal N_I)\).

Equations (3.4)--(3.5) are the precise next target. Chern-character
matching, stability, simplicity, and perfection do not imply them.

## 4. Scope firewall

- For a nonreduced CM scheme, use
  \(\mathcal N_I=\mathcal Ext^1(I,I)\) or its proven identification
  with \(\mathcal Hom(I,\mathcal O_Z)\). Do not substitute the normal
  bundle of the reduction or an associated-graded conormal algebra
  without a comparison theorem.
- The splitting is rank-one and uses a genuine trace retraction.
- This note formalizes neither the HKR/semiregularity square nor the
  global Hodge conjecture in Lean.
- The result is a reduction of the remaining obstruction space, not
  an existence or algebraicity theorem.
