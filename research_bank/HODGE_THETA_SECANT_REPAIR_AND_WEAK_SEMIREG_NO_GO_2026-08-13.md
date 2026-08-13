# Hodge theta-secant repair and weak-semiregularity obstruction

**Date:** 2026-08-13  
**Status:** Exact construction and route obstruction. This is not a proof of the Hodge conjecture.  
**Formal status:** No Lean verification. The current local Lean/workspace mount was unavailable.

## 1. Target character

Let \((X,\Theta)\) be a principally polarized complex abelian fourfold, let
\(L=\mathcal O_X(\Theta)\), and put \(x=c_1(L)\), so
\(\int_Xx^4=24\). For odd \(d\ge3\), define
\[
 v_d=1+x-\frac d2x^2-\frac d6x^3+\frac{d^2}{24}x^4.
\]
This is the normalized character \(Ae^{tx}+Be^{-tx}\), with
\(t^2=-d\), \(A+B=1\), and \(t(A-B)=1\).

For \(d=24k-1\),
\[
 e^{-x}v_d=1-12kx^2+8kx^3+(24k^2-4k)x^4. \tag{1}
\]
Thus \(E=L\otimes I_Z\) has character \(v_d\) precisely when
\[
 \operatorname{ch}(\mathcal O_Z)
 =12kx^2-8kx^3+(-24k^2+4k)x^4. \tag{2}
\]

All identities in the construction below hold in \(\mathrm{CH}^*(X)_\mathbf Q\).

## 2. Stable rank-one realization

### Theorem 2.1

For every \(k\ge1\), there is a closed subscheme \(Z\subset X\) such that
\(L\otimes I_Z\) is a rank-one torsion-free Gieseker-stable, simple,
gluable, perfect sheaf and
\[
 \operatorname{ch}(L\otimes I_Z)=v_{24k-1}.
\]

### Construction

Choose mutually disjoint smooth complete intersections
\[
 S=\operatorname{CI}(2,6k),\qquad
 C=\operatorname{CI}(2,2k,9k+1).
\]
The powers \(L^n\), \(n\ge2\), are globally generated; simultaneous
smoothness and avoidance are nonempty incidence-open conditions.

Put
\[
 N=2k(63k^2+8k+1).
\]
Write \(N=16a+36b\) with \(a,b\ge0\): since \(N/4\ge36\), choose
\(b\in\{0,1,2,3\}\) congruent to \(N/4\pmod4\) and set
\(a=(N/4-9b)/4\). Let \(P\) be a mutually disjoint union, disjoint from
\(S\cup C\), of \(a\) transverse zero-dimensional complete intersections
of multidegree \((2,2,2,2)\) and \(b\) of multidegree \((2,2,3,3)\).
Then \([P]=Nx^4\). Set \(Z=S\sqcup C\sqcup P\).

For a complete intersection of degrees \(a_i\), Koszul gives
\[
 \operatorname{ch}(\mathcal O_Y)=\prod_i(1-e^{-a_ix}). \tag{3}
\]
Consequently,
\[
\begin{aligned}
 \operatorname{ch}_2(\mathcal O_S)&=12kx^2,\\
 \operatorname{ch}_3(\mathcal O_S)&=-6k(6k+2)x^3,\\
 \operatorname{ch}_4(\mathcal O_S)&=(72k^3+36k^2+8k)x^4,\\
 \operatorname{ch}_3(\mathcal O_C)&=4k(9k+1)x^3,\\
 \operatorname{ch}_4(\mathcal O_C)&=-2k(9k+1)(11k+3)x^4.
\end{aligned}
\]
The degree-three sum is \(-8kx^3\); the degree-four sum is
\((-126k^3-40k^2+2k)x^4\). Adding \([P]\) gives (2), and (1) proves
the target identity.

The ideal is rank-one torsion-free. Every proper full-dimensional
rank-one subsheaf has a nonzero torsion quotient, whose first nonzero
Hilbert coefficient is positive, so its reduced Hilbert polynomial is
strictly smaller. Thus the sheaf is stable. Stability implies simplicity;
a sheaf has no negative self-Ext; and every coherent sheaf on smooth \(X\)
is perfect.

For \(k=1\), a point-free realization is available:
\[
 S=\operatorname{CI}(2,6),\quad
 C_1,C_2,C_3=\operatorname{CI}(2,2,2),\quad
 C_4=\operatorname{CI}(2,2,4),
\]
all mutually disjoint. Their characters sum to
\(12x^2-8x^3-20x^4\), the target (2) for \(d=23\).

## 3. Exact failure of weak semiregularity

Let
\[
 \operatorname{ev}_E:HH^2(X)\longrightarrow\operatorname{Ext}^2(E,E)
\]
be the Hochschild characteristic map. Since \(\operatorname{td}(X)=1\),
HKR identifies
\[
 HH^2(X)=H^2(\mathcal O_X)\oplus H^1(T_X)
 \oplus H^0(\wedge^2T_X).
\]
With wedge-plus-contraction convention, the characteristic/semiregularity
square is
\[
 \sigma_E(\operatorname{ev}_E(\alpha))
 =\alpha\cdot\operatorname{ch}(E). \tag{4}
\]
Hence injectivity of \(\sigma_E\) on \(\operatorname{im}(\operatorname{ev}_E)\)
is equivalent to
\[
 \ker(\operatorname{ev}_E)
 =\ker(\alpha\mapsto\alpha\cdot\operatorname{ch}(E)). \tag{5}
\]

### Theorem 3.1

Every sheaf in Theorem 2.1 fails (5). More generally, any rank-one
ideal-sheaf realization of \(v_d\) with a generically reduced lci
component of codimension at least three fails (5).

### Proof

For nonzero translation-invariant
\(\pi\in H^0(X,\wedge^2T_X)\), put
\[
 B_\pi=\tfrac12\iota_\pi(x^2),\qquad
 \alpha_\pi=(dB_\pi,0,\pi).
\]
The polarization makes \(\pi\mapsto B_\pi\) an exterior-square
isomorphism. The graded Leibniz rule gives
\[
 \iota_\pi(x^2)=2B_\pi,\quad
 \iota_\pi(x^3)=6B_\pi x,\quad
 \iota_\pi(x^4)=12B_\pi x^2.
\]
Because \(t^2=-d\), direct substitution yields
\[
 \alpha_\pi\cdot v_d=0. \tag{6}
\]

Now choose a smooth point \(p\) of an lci component \(C\) of codimension
\(r\ge3\), away from all other components, and choose \(\pi\) whose image
in \(\wedge^2N_{C/X,p}\) is nonzero. This is possible because
\(\wedge^2T_{X,p}\to\wedge^2N_{C/X,p}\) is surjective. Put
\(R=\mathcal O_{X,p}\), \(J=I_{C,p}\), and \(A=R/J\). Koszul gives
\[
 \operatorname{Ext}^2_R(A,A)\cong\wedge^2N_{C/X,p}.
\]
The characteristic action of the ambient bivector is its normal-normal
projection: degree-one normal classes multiply by the Yoneda wedge.
Naturality for the ideal triangle \(J\to R\to A\), together with
\(\operatorname{Ext}^2_R(A,R)=0\) for \(r\ge3\), sends this nonzero class
to \(\operatorname{Ext}^2_R(J,J)\). Locally \(L\) is trivial. The
\(H^2(\mathcal O_X)\) part of \(\alpha_\pi\) restricts to zero on an
affine neighborhood, so it cannot cancel the bivector action. Therefore
\[
 \operatorname{ev}_E(\alpha_\pi)\ne0. \tag{7}
\]
Equations (6)-(7) disprove (5).

For the ample complete-intersection curves above, every nonzero \(\pi\)
fails. Rank-four \(\pi\) has nonzero normal projection at every tangent
line. If rank-two \(\pi=u\wedge v\) vanished normally everywhere, every
tangent line would lie in \(\langle u,v\rangle\), so a nonzero invariant
one-form annihilating that plane would restrict to zero on the curve,
contrary to weak Lefschetz.

The kernel equality (5) is invariant under Fourier--Mukai equivalence:
Morita invariance transports Hochschild cohomology, self-Ext, the
characteristic action, and the cohomological Mukai action. Applying an
autoequivalence cannot repair these examples.

## 4. A corrected two-term secant object and its fatal local summand

There is a sharper \(d=23\) numerical repair on a genus-four Jacobian.
Let \(X=J(C)\) for nonhyperelliptic \(C\), and let
\(i:S=W_2(C)=C^{(2)}\hookrightarrow X\). Standard Macdonald--Poincare
identities give
\[
 i_*1=x^2/2,\qquad i_*K_S=2x^3/3,\qquad \chi(\mathcal O_S)=3.
\]
One can construct a simple rank-24 bundle \(V\) on \(S\) with a section,
\(c_1(V)=0\), \(c_2(V)=552\), and \(\chi(V)=-480\). Explicitly, set
\(D=\theta-3\eta\), so \(D^2=-3\), \(D\cdot K_S=1\), \(D\cdot\theta=0\),
take 23 distinct Picard-zero twists of \(\mathcal O_S(t_iD)\) with
\[
(t_i)=(-10,-10,-8,-4,-4,\underbrace{2,\ldots,2}_{18}),
\]
and a nonsplit extension
\[
 0\to\mathcal O_S\to V\to\bigoplus_iM_i\to0
\]
with every extension component nonzero. The sums
\(\sum t_i=0\), \(\sum t_i^2=368\) give \(c_2(V)=552\); slope-zero and
distinct twists kill off-diagonal Homs; nonzero extension components
force \(\operatorname{End}(V)=\mathbf C\).

GRR yields
\[
 \operatorname{ch}(i_*V)=12x^2-8x^3-20x^4.
\]
Thus
\[
 P=[\mathcal O_X\to i_*V]\otimes L
\]
is perfect, simple, and has \(\operatorname{ch}(P)=v_{23}\).

It nevertheless fails weak semiregularity. At a point where the section
is a subbundle, let \(A=R/I_S\). Locally
\[
 P\simeq I_S\oplus A[-1]^{23}.
\]
Choose a constant bivector with nonzero normal-normal projection. The
class \((23B_\pi,0,\pi)\) annihilates \(v_{23}\), while its \(H^2(\mathcal
O)\) component vanishes on the affine local chart and its evaluation on
each \(A[-1]\) diagonal is the nonzero Koszul class in
\(\operatorname{Ext}^2_R(A,A)=\wedge^2N_{S/X}\). Hence
\(\operatorname{ev}_P(\alpha_\pi)\ne0\).

More generally, every two-term surface construction
\([\mathcal O_X\to i_*V]\) with \(\operatorname{rank}V>1\) and a regular
subbundle section has the same fatal supported summand.

## 5. Split Hilbert--Burch no-go

A pure codimension-two Cohen--Macaulay quotient is the remaining
rank-one escape, but the most natural split determinantal construction
is impossible.

Suppose a minimal theta-power Hilbert--Burch resolution (Picard-zero
twists allowed) is
\[
 0\to\bigoplus_{i=1}^rL^{-b_i}
 \to\bigoplus_{j=1}^{r+1}L^{-a_j}\to I_Z\to0,
\]
with sorted nonnegative \(a_j,b_i\) and every signed maximal minor
nonzero. The minor deleting row one gives a perfect matching in the
allowed-entry graph, hence \(b_i\ge a_{i+1}\). Since \(c_1(I_Z)=0\),
\(\sum a_j=\sum b_i\). Therefore
\((0,b_1,\ldots,b_r)\) majorizes
\((a_1,\ldots,a_{r+1})\). Karamata for \(t^4\) yields
\[
 \sum b_i^4\ge\sum a_j^4.
\]
But target (2) requires
\[
 \sum a_j^4-\sum b_i^4=24(24k^2-4k)>0,
\]
a contradiction. This excludes only globally split theta-line
Hilbert--Burch resolutions; arbitrary vector-bundle resolutions remain.

## 6. Exact remaining target

The construction closes character, integrality, stability, simplicity,
gluability, and perfection, but not weak semiregularity.

Any rank-one torsion-free target sheaf is
\((L\otimes P)\otimes I_Z\), \(P\in\operatorname{Pic}^0(X)\). The local
certificate kills every realization with a generically reduced lci
component of codimension at least three. A codimension-two CM ideal has
local projective dimension one, so that specific local
\(\operatorname{Ext}^2\) certificate disappears. Smooth and normal-CM
surface candidates are excluded by the forced negative Euler
characteristic and generic vanishing in the applicable class.

The precise surviving sheaf target is therefore a nonnormal or
nonreduced pure codimension-two CM surface with an exact global kernel
calculation, or a genuinely derived complex with local characteristic
cancellation. Split theta-line Hilbert--Burch and supported-rank \(>1\)
two-term constructions are ruled out.

## 7. Provenance and scope

Motivation: Eyal Markman, *Secant sheaves and Weil classes on abelian
varieties*, arXiv:2509.23403v2, especially Question 11.4 and Section 12.
Formal inputs: HKR, Atiyah-class characteristic action,
Buchweitz--Flenner/Pridham semiregularity, Koszul Ext, Bertini, weak
Lefschetz, GRR, and Hilbert--Burch. Giuseppe Pareschi,
arXiv:1401.7442, proves generic vanishing for **normal Cohen--Macaulay**
subvarieties of abelian varieties; no broader Euler-sign statement is
used.

This note constructs no exceptional Hodge class and proves no case of
the Hodge conjecture. Novelty has not been established.
