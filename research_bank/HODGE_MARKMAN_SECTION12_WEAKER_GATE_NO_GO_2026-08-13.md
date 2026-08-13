# Markman Section 12 partial-normalization secant objects fail the weaker gate

**Date:** 2026-08-13  
**Status:** exact local obstruction applied directly to the published v2 family;
research audit, not a Hodge result  
**Source audited:** Eyal Markman, *Secant sheaves and Weil classes on abelian
varieties*, arXiv:2509.23403v2, Section 12, especially the object in lines
547--552 of the arXiv HTML and Question 11.4 in lines 522--526  
**Conclusion:** for every odd \(d\geq3\), the Section 12
partial-normalization secant object does not satisfy the proposed weaker
hypothesis that semiregularity be injective on the image of Hochschild
evaluation.

## 1. Exact published setup

Let \((X,\Theta)\) be a principally polarized abelian fourfold, let \(d\geq3\)
be odd, and put
\[
 K=\mathbf Q(\sqrt{-d}),\qquad n=(d+9)/2.
\]
Markman chooses generic translates \(D_i\) of \(\Theta\), defines
\[
 Z_i=D_i\cap D_{i+1},\qquad Z=\bigcup_i Z_i,
\]
and takes a partial normalization
\[
 \nu:\widetilde Z\longrightarrow Z
\]
along a specified positive number of isolated transverse self-intersection
points.  The Section 12 object is
\[
 E=\left[\mathcal O_X\longrightarrow\nu_*\mathcal O_{\widetilde Z}\right]
 \otimes\mathcal O_X(\Theta). \tag{1}
\]
The paper states
\[
 \operatorname{ch}(E)\in
 \operatorname{span}\{
 e^{\sqrt{-d}\Theta},e^{-\sqrt{-d}\Theta}\}. \tag{2}
\]
Question 11.4 asks whether the general semiregularity theorem still holds
under the weaker assumption that
\[
 \sigma_E|_{\operatorname{im}ev_E}
\]
is injective.  Section 12 says it remained to check this weaker criterion
for (1).

The argument below checks it negatively.  It applies to the Section 12
family itself; it is not merely an obstruction to a repaired numerical
variant.

Primary source:
<https://arxiv.org/html/2509.23403v2>, Section 12 and Question 11.4.

## 2. Local model at a selected normalized crossing

Choose one isolated self-intersection point selected for partial
normalization. Genericity in the published construction makes the two
codimension-two branches smooth and transverse, with no third branch at that
isolated point. Complete locally:
\[
 R=\mathbf C[[u,v,w,z]],\quad
 A=R/(u,v),\quad B=R/(w,z).
\]
Partial normalization separates the two branches, so (1), before the harmless
line-bundle twist, is locally
\[
 P=[R\longrightarrow A\oplus B]. \tag{3}
\]
Resolving \(A,B\) by Koszul complexes, taking the cone, and canceling the
unique unit pair gives the minimal cochain complex
\[
 R^2\xrightarrow{D_0}R^4\xrightarrow{D_1}R,
\]
where
\[
D_0=
\begin{pmatrix}
-v&0\\u&0\\0&-z\\0&w
\end{pmatrix},
\qquad
D_1=(u,v,-w,-z). \tag{4}
\]
Changing the global signs of a row or differential does not affect the
certificate. Directly, \(D_1D_0=0\), and all entries lie in the maximal ideal
\(\mathfrak m=(u,v,w,z)\).

With trivial connections, the degree-two component of the Atiyah exponential
is represented, up to one cochain-convention sign, by
\[
 \frac12dD_1\wedge dD_0
 =
 (-du\wedge dv,\;dw\wedge dz):
 R^2\longrightarrow R\otimes\Omega_R^2. \tag{5}
\]
For
\[
 \pi=\partial_u\wedge\partial_v,
\]
contraction is the constant row
\[
 c_\pi=(-1,0). \tag{6}
\]
Every degree-two boundary is
\[
 D_1h^{-1}+h^0D_0. \tag{7}
\]
Every entry of (7) lies in \(\mathfrak m\), whereas (6) has a unit entry.
Therefore
\[
 [c_\pi]\neq0\in\operatorname{Ext}^2_R(P,P). \tag{8}
\]
This is independent of the sign convention and of tensoring by
\(\mathcal O_X(\Theta)\), which is locally trivial.

The same certificate is encoded in the existing finite local Lean model in
the research bank; the global attribution in this note is a human proof and
has not received a fresh Lean kernel replay.

## 3. A global Hochschild class in the Chern annihilator

Let \(x=c_1(\Theta)\), let \(\pi\) be a translation-invariant global bivector,
and set
\[
 B_\pi=\frac12\iota_\pi(x^2),\qquad
 \alpha_\pi=(dB_\pi,0,\pi)
 \in H^2(\mathcal O_X)\oplus H^1(T_X)\oplus
 H^0(\wedge^2T_X). \tag{9}
\]
The polarization identifies invariant tangent and cotangent spaces, so one
can choose a global invariant \(\pi\) whose value at the selected point has
the branch-normal component \(\partial_u\wedge\partial_v\).

Put \(t=\sqrt{-d}\), so \(t^2=-d\). For either sign,
\[
 \iota_\pi(e^{\pm tx})=t^2B_\pi e^{\pm tx}
 =-dB_\pi e^{\pm tx}. \tag{10}
\]
Under the wedge-plus-contraction HKR action, (9)--(10) give
\[
 \alpha_\pi\cdot e^{\pm tx}=0. \tag{11}
\]
By (2),
\[
 \alpha_\pi\cdot\operatorname{ch}(E)=0. \tag{12}
\]
If the opposite HKR sign convention is used, the sign of the
\(H^2(\mathcal O_X)\) component changes coherently; the conclusion is
unchanged.

## 4. Global evaluation remains nonzero

The \(H^2(\mathcal O_X)\) component \(dB_\pi\) restricts to zero on the
formal affine neighborhood \(\operatorname{Spec}R\). The \(H^1(T_X)\)
component is zero. Hence localization of the characteristic evaluation is
exactly the bivector class (6):
\[
 \operatorname{ev}_E(\alpha_\pi)|_{\operatorname{Spec}R}
 =[c_\pi]\neq0. \tag{13}
\]
If the global Ext class were zero, every localization would be zero, so
\[
 \operatorname{ev}_E(\alpha_\pi)\neq0. \tag{14}
\]

The characteristic/semiregularity square on an abelian variety is
\[
 \sigma_E(\operatorname{ev}_E(\alpha))
 =\alpha\cdot\operatorname{ch}(E). \tag{15}
\]
Equations (12), (14), and (15) give a nonzero element
\[
 \operatorname{ev}_E(\alpha_\pi)
 \in\ker\!\left(
 \sigma_E|_{\operatorname{im}ev_E}
 \right). \tag{16}
\]
Therefore
\[
 \boxed{\sigma_E|_{\operatorname{im}ev_E}\text{ is not injective}.}
 \tag{17}
\]

## 5. Exact scope

The count of selected normalized isolated crossings in Section 12 is positive
for every odd \(d\geq3\), so one selected point suffices for every member of
the stated family.  The result uses only:

1. a selected isolated crossing of two smooth transverse codimension-two
   branches;
2. partial normalization separating those branches;
3. the secant character statement (2).

It does not depend on which other isolated points are normalized, on global
simplicity, or on the exact coefficients in the secant span.

This conclusion does **not** answer the abstract first sentence of Question
11.4: it does not prove or disprove a general semiregularity theorem under
the weaker hypothesis. It proves that Markman's Section 12 candidate family
fails the antecedent weaker hypothesis.

It also does not affect the earlier sixfold theorem in Sections 11.4--11.5,
where Markman descends to a quotient and proves actual equivariant
semiregularity by a different argument.

## 6. Conditional pure-translation equivariant salvage no-go

This obstruction also closes one natural equivariant repair, under explicit
descent hypotheses. The reference is Alexander Perry,
[arXiv:2604.00511v2](https://arxiv.org/abs/2604.00511), Definition 2.6 and
Remark 6.6 (version dated 2026-06-24). Definition 2.6 says that an object is
weakly \(G\)-semiregular when some equivariant lift is semiregular in the
invariant category. Remark 6.6 identifies, for a finite subgroup acting only
by translations,
\[
 \operatorname{D}_{\mathrm{perf}}(X)^G
 \simeq \operatorname{D}_{\mathrm{perf}}(X/G).
 \tag{8}
\]

Let \(G\subset X\) be a finite translation subgroup, let
\(p:X\to Y=X/G\) be the quotient isogeny, and assume all of the following:

1. the Section 12 object \(E\) admits a \(G\)-linearization;
2. the selected normalized crossings form a \(G\)-stable set, and the
   partial-normalization data are equivariant;
3. at least one selected crossing occurs (hence its free \(G\)-orbit
   descends to a crossing of the same étale-local type on \(Y\)).

For any chosen linearization, let \(\bar E\in
\operatorname{D}_{\mathrm{perf}}(Y)\) be the descended object. The class
\(\alpha\) from (3) is translation invariant. Since an isogeny of complex
abelian varieties induces isomorphisms on the HKR summands, it has a unique
preimage
\[
 p^*\bar\alpha=\alpha,\qquad
 \bar\alpha\in\operatorname{HH}^2(Y). \tag{9}
\]
Naturality of the characteristic action gives
\[
 p^*\operatorname{ev}_{\bar E}(\bar\alpha)
 =\operatorname{ev}_{E}(\alpha). \tag{10}
\]
The right side is nonzero by the unit local certificate (6). Equivalently,
the free orbit of selected nodes becomes one node on \(Y\), and an étale
chart has exactly the same separated-branch resolution (4). Pullback on
Ext is injective: the normalized trace splits
\(\mathcal O_Y\to p_*\mathcal O_X\). Thus
\(\operatorname{ev}_{\bar E}(\bar\alpha)\ne0\).

On the other hand,
\[
 p^*\bigl(\bar\alpha\cdot\operatorname{ch}(\bar E)\bigr)
 =\alpha\cdot\operatorname{ch}(E)=0. \tag{11}
\]
Pullback on rational cohomology is injective, again by normalized trace, so
the class inside parentheses vanishes. The characteristic
action--semiregularity identity therefore shows that
\(\sigma_{\bar E}\) kills the nonzero class
\(\operatorname{ev}_{\bar E}(\bar\alpha)\). Hence \(\bar E\) is not
semiregular, and \(E\) is not weakly \(G\)-semiregular for any compatible
linearization.

There is no cancellation from averaging the node orbit: the quotient is
finite étale, translations have identity differential, and the orbit
descends to a single copy of the same nonzero local unit. This theorem is
conditional on a genuine pure-translation linearization and equivariant
partial-normalization data. It does not cover translation--tensor actions,
nonfree actions, or an abstract categorical action not realized by this
quotient descent.

## 7. Claim, local countercertificate, best salvage

**Claim settled.** The Section 12 objects do not pass the proposed weaker
semiregularity gate.

**Finite countercertificate.** The unit row \((-1,0)\) in (6) is a
nonboundary because all boundaries vanish modulo \(\mathfrak m\), while the
global class producing it annihilates the full secant span.

**Best salvage.** Replace the partially normalized transverse union by a
pure codimension-two CM architecture whose minimal local resolution is
two-term, or build a genuinely derived local complex in which the branch
Atiyah-square classes cancel before localization. Merely changing the
selection of normalized crossings cannot repair any candidate with at least
one separated transverse crossing.

No Hodge class is proved algebraic here, and no Millennium theorem is proved.
