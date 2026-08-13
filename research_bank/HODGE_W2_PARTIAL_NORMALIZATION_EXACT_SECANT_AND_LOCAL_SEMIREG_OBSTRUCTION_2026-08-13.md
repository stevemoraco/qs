# Exact \(W_2\) partial-normalization secant objects and a local weak-semiregularity obstruction

**Date:** 2026-08-13  
**Status:** GREEN for the exact Chern-character, perfectness, and simplicity theorems below; RED for the proposed weak-semiregularity bridge. This is **not** a proof of the Hodge conjecture.  
**Scope:** principally polarized Jacobian fourfolds \(X=J(C)\) of nonhyperelliptic genus-four curves, rational Chow/cohomology, and the standard Hochschild characteristic-action/semiregularity square. No Lean verification is claimed.

## 1. Target

Let \(x=c_1(\Theta)\) on the principally polarized abelian fourfold \(X\), normalized by
\[
\int_X x^4=4!=24.
\]
For odd \(d\), put
\[
v_d
 =1+x-\frac d2x^2-\frac d6x^3+\frac{d^2}{24}x^4.
\]
Equivalently, if \(t^2=-d\), then \(v_d=Ae^{tx}+Be^{-tx}\), where
\[
A+B=1,\qquad t(A-B)=1.
\]

We construct an exact simple perfect object with this character for every
\[
d=24k-1,\qquad k\ge1,
\]
and then give a finite local certificate showing that it is not weakly semiregular.

## 2. Geometry of \(W_2(C)\)

Let \(C\) be a nonhyperelliptic genus-four curve and let
\[
S=W_2(C)\cong C^{(2)}\hookrightarrow X=J(C).
\]
The Abel map is a smooth embedding because \(C\) has no \(g^1_2\). Poincaré's formula and Macdonald's symmetric-product calculation give
\[
[S]=\frac{x^2}{2},\qquad
\operatorname{ch}(\mathcal O_S)
 =\frac{x^2}{2}-\frac{x^3}{3}+\frac{x^4}{8}.
\]
In particular,
\[
\#(S\cap(S+a))=\int_X\left(\frac{x^2}{2}\right)^2=6
\]
for a transverse translate.

Fix \(N=24k\) general translates
\[
S_i=S+a_i,\qquad 1\le i\le N.
\]
Kleiman transversality and finitely many simultaneous open conditions give:

1. every pair \(S_i,S_j\) meets transversely in six reduced points;
2. no three surfaces meet;
3. all pairwise intersection points are distinct.

Hence their union
\[
Z=\bigcup_{i=1}^{N}S_i
\]
has exactly
\[
m=6\binom{24k}{2}=72k(24k-1)
\]
ordinary transverse double points.

Let \(n:\bigsqcup_iS_i\to Z\) be the normalization. There is an exact conductor sequence
\[
0\longrightarrow\mathcal O_Z
 \longrightarrow n_*\mathcal O_{\bigsqcup S_i}
 \longrightarrow\bigoplus_{p\in\mathrm{Sing}(Z)}k_p
 \longrightarrow0.
\]

## 3. Separate exactly two-thirds of the nodes

Choose a subset \(T\subset\mathrm{Sing}(Z)\) of size
\[
q=48k(24k-1)=\frac23m.
\]
For example, choose four of the six nodes belonging to every unordered pair \(\{i,j\}\). Define the partial-normalization algebra \(\mathcal Q\) as the inverse image of
\(\bigoplus_{p\in T}k_p\) in the conductor quotient. Then
\[
0\longrightarrow\mathcal O_Z
 \longrightarrow\mathcal Q
 \longrightarrow\mathcal O_T
 \longrightarrow0.
\]
Locally, \(\mathcal Q\) equals the direct sum of the two branch rings at \(p\in T\), and equals their fiber product at an unseparated node.

Inclusion-exclusion gives
\[
\begin{aligned}
\operatorname{ch}(\mathcal O_Z)
 &=24k\operatorname{ch}(\mathcal O_S)-m[\mathrm{pt}]\\
 &=12kx^2-8kx^3+3kx^4-\frac{m}{24}x^4\\
 &=12kx^2-8kx^3+(-72k^2+6k)x^4.
\end{aligned}
\]
Since \([\mathrm{pt}]=x^4/24\), partial normalization adds
\[
\operatorname{ch}(\mathcal O_T)=\frac{q}{24}x^4=(48k^2-2k)x^4.
\]
Therefore
\[
\boxed{\operatorname{ch}(\mathcal Q)
 =12kx^2-8kx^3+(-24k^2+4k)x^4.}
\]

Put
\[
P=[\mathcal O_X\longrightarrow\mathcal Q]
\]
in cohomological degrees \(0,1\), and set
\[
E=P\otimes\mathcal O_X(\Theta).
\]
Then
\[
\operatorname{ch}(E)
 =e^x(1-\operatorname{ch}(\mathcal Q))
 =v_{24k-1}.
\]

### Theorem 3.1 — exact secant object

For every \(k\ge1\), the preceding construction gives a perfect object \(E\in D^b(X)\) satisfying
\[
\operatorname{ch}(E)=v_{24k-1}
\]
in \(\mathrm{CH}^*(X)_{\mathbf Q}\), hence in rational cohomology.

For \(k=1\), this uses 24 translates, 1656 transverse nodes, and 1104 separated nodes, and gives \(v_{23}\).

## 4. The separated-node local model

At \(p\in T\), use
\[
R=\mathbf C[[u,v,w,z]],\qquad
I_1=(u,v),\qquad I_2=(w,z).
\]
The two branches have rings \(A=R/I_1\) and \(B=R/I_2\), and locally
\[
P=(R\longrightarrow A\oplus B).
\]
Resolving \(A,B\) by their Koszul complexes, taking the mapping cone, and cancelling the unique constant contractible pair gives the minimal cochain complex
\[
F^{-1}=R^2\xrightarrow{D_0}F^0=R^4\xrightarrow{D_1}F^1=R,
\]
where
\[
D_0=
\begin{pmatrix}
-v&0\\
 u&0\\
 0&-z\\
 0&w
\end{pmatrix},
\qquad
D_1=(-u,-v,w,z).
\]
Direct multiplication gives \(D_1D_0=0\), and all entries lie in the maximal ideal
\(\mathfrak m=(u,v,w,z)\). Its cohomology is
\[
H^0(F)=I_1\cap I_2=I_1I_2,\qquad H^1(F)=k_p.
\]
This finite free model proves local perfectness at the only nontrivial partial-normalization points. The smooth branches and unseparated transverse union also have finite projective dimension, so \(P\) and \(E\) are globally perfect.

## 5. Simplicity

The Postnikov triangle is
\[
I_Z\longrightarrow P\longrightarrow\mathcal O_T[-1]\xrightarrow{\delta}I_Z[1].
\]
At a transverse node, \(\operatorname{depth}(I_Z)=2\), hence
\[
\operatorname{Ext}^1(\mathcal O_T,I_Z)=0.
\]
Moreover,
\[
\mathcal Hom(I_Z,I_Z)=\mathcal O_X
\]
because \(X\) is normal and \(I_Z=\mathcal O_X\) in codimension one, so globally
\[
\operatorname{End}(I_Z)=\mathbf C.
\]

For every \(p\in T\), the local component
\[
\delta_p\in\operatorname{Ext}^2(k_p,I_Z)
\]
is nonzero. One exact proof uses uniqueness of minimal free resolutions: if \(\delta_p=0\), then locally \(P\) would split as \(I_Z\oplus k_p[-1]\), whose minimal resolution contains the length-four Koszul resolution of \(k_p\); this cannot be isomorphic to the displayed three-term minimal model.

Thus an endomorphism of \(P\) injects into
\[
\operatorname{End}(I_Z)\oplus\operatorname{End}(\mathcal O_T)
\]
and must stabilize every nonzero \(\delta_p\). The scalar on each \(k_p\) is therefore equal to the single global scalar on \(I_Z\).

### Theorem 5.1 — simplicity

\[
\boxed{\operatorname{End}_{D^b(X)}(P)=\mathbf C.}
\]
Consequently \(E=P(\Theta)\) is simple and perfect.

No connectedness assumption on the remaining glued-node incidence graph is needed.

## 6. Exact Atiyah-square certificate

Use trivial connections on the free modules of \(F\). The Atiyah cocycle is represented by
\[
a^{-1}=dD_0,\qquad a^0=dD_1.
\]
The degree-two component is
\[
\left(\frac{a^2}{2}\right)^{-1}
 =\frac12\,dD_1\wedge dD_0
 =(du\wedge dv,\,-dw\wedge dz):
 F^{-1}\longrightarrow F^1\otimes\Omega_R^2,
\]
up to a single harmless global sign determined by the cochain convention.

For a bivector \(\pi\), contraction gives the degree-two endomorphism cocycle
\[
c_\pi
 =\bigl(\pi(du,dv),-\pi(dw,dz)\bigr):F^{-1}\to F^1.
\]
Every degree-two boundary has the form
\[
D_1h^{-1}+h^0D_0
\]
for degree-one maps \(h^{-1},h^0\). Every entry of such a boundary belongs to \(\mathfrak m\), because every entry of \(D_0,D_1\) lies in \(\mathfrak m\). Therefore any \(c_\pi\) with a nonzero constant component is not null-homotopic. In particular,
\[
\pi=\partial_u\wedge\partial_v
\quad\Longrightarrow\quad
c_\pi=(1,0)\ne0
\]
in \(\operatorname{Ext}^2_R(F,F)\).

This is a finite local certificate: cocyclehood is automatic from the amplitude \([-1,1]\), while evaluation at \(u=v=w=z=0\) separates the constant row from all boundaries.

## 7. Failure of weak semiregularity

On an abelian fourfold,
\[
HH^2(X)=H^2(\mathcal O_X)\oplus H^1(T_X)\oplus H^0(\Lambda^2T_X),
\]
and \(\operatorname{td}(X)=1\).

For a translation-invariant bivector \(\pi\), set
\[
B_\pi=\frac12\iota_\pi(x^2),\qquad
\alpha_\pi=((24k-1)B_\pi,0,\pi).
\]
Since \(x\) has Hodge type \((1,1)\),
\[
\iota_\pi(x^j)=j(j-1)B_\pi x^{j-2}.
\]
Equivalently, for \(t^2=-(24k-1)\),
\[
\iota_\pi(e^{\pm tx})=t^2B_\pi e^{\pm tx}.
\]
It follows exactly that
\[
\alpha_\pi\cdot v_{24k-1}=0.
\]
(The alternative HKR sign convention changes both signs coherently.)

Choose a separated node \(p\), and choose a global translation-invariant bivector whose normal-normal projection to one local branch is \(\partial_u\wedge\partial_v\). On the affine formal neighborhood \(\operatorname{Spec}R\), the \(H^2(\mathcal O_X)\) component restricts to zero. Thus the localization of the characteristic evaluation is precisely the unit-entry cocycle
\[
\operatorname{ev}_E(\alpha_\pi)|_p=c_\pi=(1,0)\ne0.
\]
Hence the global Ext class is nonzero.

The characteristic-action/semiregularity square gives
\[
\sigma_E(\operatorname{ev}_E(\alpha))
 =\alpha\cdot\operatorname{ch}(E).
\]
Therefore
\[
\alpha_\pi\in
 \ker(\alpha\mapsto\alpha\cdot\operatorname{ch}(E))
 \setminus\ker(\operatorname{ev}_E).
\]

### Theorem 7.1 — local weak-semiregularity obstruction

For every \(k\ge1\), the exact simple perfect object constructed above is **not weakly semiregular**:
\[
\ker(\operatorname{ev}_E)
 \ne
\ker(\alpha\mapsto\alpha\cdot\operatorname{ch}(E)).
\]
Equivalently, \(\sigma_E\) is not injective on \(\operatorname{im}(\operatorname{ev}_E)\).

Thus correcting every Chern-character coefficient and proving simplicity/perfectness does not close Markman's deformation gate.

## 8. Glued nodes do not provide an easy escape

At an unseparated transverse node, the union ideal
\[
I=(u,v)(w,z)
\]
has a minimal tensor-product resolution. One obtains a degree-two Atiyah-square column
\[
(-dv\wedge dz,\;dv\wedge dw,\;du\wedge dz,\;-du\wedge dw).
\]
Contracting, for example, with \(\partial_u\wedge\partial_w\) gives a unit component. Minimality again implies non-null-homotopy. Hence both choices fail locally:

- separated nodes fail through a pure branch-normal bivector;
- glued transverse nodes fail through a cross-branch bivector.

Changing which nodes are separated cannot repair weak semiregularity within this transverse-union architecture.

## 9. Claimant / critic / rebuilder

**Claimant.** The coefficient defect in the printed secant construction can be repaired exactly. The family above supplies a simple perfect geometric object with the full target \(v_{24k-1}\), not merely the correct rank or low Chern classes.

**Critic.** The explicit minimal local resolution exposes a constant Atiyah-square cocycle. It is killed by the Hodge-character derivative only after adding the global \(H^2(\mathcal O_X)\) component, which disappears upon localization. Therefore the semiregularity map has a nonzero kernel on the evaluated image.

**Rebuilder.** The viable rank-one escape is now sharply restricted. A pure codimension-two Cohen–Macaulay ideal has local projective dimension one and no local \(\operatorname{Ext}^2(I,I)\) term, whereas these nodal unions are not Cohen–Macaulay and have the fatal local cocycle. A future construction must use a genuinely pure CM surface with a nonsplit higher Hilbert–Burch resolution and must avoid both the normal-CM Euler obstruction and the split theta-line/semihomogeneous resolution no-gos.

## 10. Scope and provenance

Primary ingredients:

- I. G. Macdonald, *Symmetric products of an algebraic curve*, Topology 1 (1962), for \(C^{(2)}\);
- Poincaré's formula for \(W_d(C)\subset J(C)\);
- Kleiman transversality for general translates;
- the standard Atiyah-class characteristic morphism and Buchweitz–Flenner/Pridham semiregularity square;
- E. Markman, *Secant sheaves and Weil classes on abelian varieties*, arXiv:2509.23403v2, for the target and weak-semiregularity strategy.

This note does **not** prove an algebraic Hodge class outside the known algebra, does not prove formal deformation over a Hodge locus, and does not prove the Hodge conjecture. It is an exact constructive repair followed by an exact local obstruction. Novelty has not been externally audited. No Lean compilation, kernel replay, or axiom audit has been performed.
