# Hodge theta target: Cohen--Macaulay Du Bois and curve-defect obstruction

**Date:** 2026-08-13  
**Status:** GREEN conditional only on the cited generic-vanishing and local-cohomological-dimension theorems; independently reconstructed and hostile-audited.  
**Millennium status:** no proof of the Hodge conjecture. No Lean verification is claimed.

## 1. Exact target

Let \((A,\Theta)\) be a principally polarized complex abelian fourfold,
write \(x=c_1(\Theta)\), and normalize
\(\int_Ax^4=4!=24\). For \(k\ge1\), the theta-secant target
\(d=24k-1\) forces any pure codimension-two quotient \(Z\), if it
exists, to have

\[
 \operatorname{ch}(\mathcal O_Z)
 =12k x^2-8k x^3+(-24k^2+4k)x^4.
\]

Thus

\[
 \chi(\mathcal O_Z)
 =96k(1-6k)=-96k(6k-1)<0. \tag{1.1}
\]

The sign in (1.1) is the entire input from the proposed Hodge
construction.

## 2. Imported exact theorems

We use the following source-backed statements.

1. If \(Z\) is an arbitrary Cohen--Macaulay complex surface, then its
   local cohomological defect is zero:
   \[
     \operatorname{lcdef}(Z)=0. \tag{2.1}
   \]
   Vo records this explicitly in Example 9.2(2) of
   arXiv:2410.11109, citing Ogus and Dao--Takagi. Equivalently, for an
   embedding into a smooth variety, local cohomology is concentrated
   in the codimension.

2. If \(M\) is a mixed Hodge module on an abelian variety, then every
   Hodge-graded de Rham object
   \(\operatorname{gr}^F_j\operatorname{DR}(M)\) is a GV object
   (Popa--Schnell, quoted as Vo Theorem 6.1).

3. Vo Theorem 4.3 identifies the cohomological amplitude of
   \[
     \mathbf D_Z(\mathbb Q_Z^H[2])
   \]
   with the local cohomological defect. In particular, (2.1) makes
   this dual constant-Hodge-module complex an honest mixed Hodge
   module, concentrated in degree zero.

4. The Hodge-module/Du-Bois identification and duality give
   \[
   \operatorname{gr}^F_0\operatorname{DR}
      \bigl(\mathbf D_Z(\mathbb Q_Z^H[2])\bigr)
   \cong
   \mathbb D_Z(\underline\Omega_Z^0)[-2]. \tag{2.2}
   \]

These statements hold in the derived categories indicated. No
ordinary-resolution replacement for the Du Bois complex is used.

## 3. The reduced CM Du Bois no-go

### Theorem 3.1

Let \(i:Z\hookrightarrow A\) be a reduced, pure, projective
Cohen--Macaulay surface in a complex abelian variety. If \(Z\) has Du
Bois singularities, then

\[
 \chi(\mathcal O_Z)\ge0. \tag{3.1}
\]

Consequently no such \(Z\) can realize the target (1.1).

### Proof

By (2.1),
\[
 M:=\mathbf D_Z(\mathbb Q_Z^H[2])
\]
is an honest mixed Hodge module. A closed immersion is finite, hence
its pushforward is t-exact for the perverse/MHM t-structure, so
\(i_*M\) is a mixed Hodge module on \(A\). Theorem 6.1 and
proper-pushforward compatibility of the Hodge filtration give that

\[
 i_*F,\qquad
 F:=\mathbb D_Z(\underline\Omega_Z^0)[-2],
 \tag{3.2}
\]
is a GV sheaf.

Because \(Z\) is Du Bois,
\(\underline\Omega_Z^0\simeq\mathcal O_Z\). Because \(Z\) is a
Cohen--Macaulay surface,
\[
 \mathbb D_Z(\mathcal O_Z)[-2]\simeq\omega_Z.
\]
Thus \(i_*\omega_Z\) is GV. For a general
\(\alpha\in\operatorname{Pic}^0(A)\), all higher cohomology vanishes,
so
\[
 \chi(\omega_Z)=h^0(Z,\omega_Z\otimes i^*\alpha)\ge0.
\]
Cohen--Macaulay Serre duality in dimension two gives
\(\chi(\omega_Z)=\chi(\mathcal O_Z)\), proving (3.1). This contradicts
(1.1). \(\square\)

The proof does not require normality or irreducibility. For a
reducible equidimensional \(Z\), the direct mixed-Hodge-module
argument is used rather than Vo's irreducibly stated Theorem B.

### Corollary 3.2

A reduced pure Cohen--Macaulay target with character (1.1) must be
non-Du-Bois. In particular it cannot be SNC, semilog canonical, or any
other reduced singularity class known to be Du Bois.

This is substantially stronger than the normal-CM generic-vanishing
obstruction: nonnormal and reducible Du Bois surfaces are also
excluded.

## 4. Exact frontier without an unproved cokernel sign

For a general reduced CM surface the natural Du Bois morphism
\(\mathcal O_Z\to\underline\Omega_Z^0\) dualizes to a morphism
\[
 \mathbb D_Z(\underline\Omega_Z^0)[-2]\longrightarrow\omega_Z.
\]
The source is a GV sheaf when \(\operatorname{lcdef}(Z)=0\). However,
the cited results do **not** by themselves prove that this degree-zero
map is injective, nor that its cokernel is a sheaf with a controlled
Euler sign. Consequently this note makes no quantitative claim about
the dimension of the non-Du-Bois locus or an Euler debt carried by a
cokernel.

The exact surviving conclusion is only that a reduced CM target cannot
be Du Bois everywhere. Whether isolated non-Du-Bois points already
suffice, or a curve of non-Du-Bois singularities is forced, remains an
open bridge here.

## 5. Claimant / critic / rebuilder

**Claimant.** A reduced, nonnormal, Cohen--Macaulay surface with a
curve singular locus might evade the earlier normal-CM and isolated
lci obstructions.

**Critic.** If its singularities are Du Bois, mixed-Hodge-module
generic vanishing forces \(\chi(\mathcal O_Z)\ge0\), opposite to the
required value. The cited generic-vanishing argument gives no sign for the cone or
cokernel of the dual Du Bois morphism away from the Du Bois case; that
stronger inference was removed under hostile audit.

**Rebuilder.** The reduced frontier is now precise: construct a pure CM surface with genuinely non-Du-Bois singularities
while also closing the characteristic-action/semiregularity gate. The other
remaining frontier is generically nonreduced CM structure, to which
the reduced Du Bois complex does not directly apply.

## 6. Hostile scope audit

### A killed overgeneralization

The implication
\[
 \text{Cohen--Macaulay}\Longrightarrow\operatorname{lcdef}=0
\]
is special in the dimensions used here; it is false without a
dimension bound. In characteristic zero, the height-two ideal of
\(2\times2\) minors of a generic \(2\times3\) matrix has a
four-dimensional Cohen--Macaulay quotient but cohomological dimension
three. This prevents extrapolating the surface theorem to arbitrary
CM dimension.

### A second killed bridge

Du Bois singularities do **not** imply
\(\mathcal O_Z\simeq Rf_*\mathcal O_Y\) for one ordinary resolution.
That is a rational-singularity property. Nodal curves already
separate the two notions. The proof above instead uses the actual
Du Bois complex and its mixed-Hodge-module realization.

### Nonreduced scope

The theorem is for reduced \(Z\). The constant Hodge module and
\(\underline\Omega_Z^0\) see the reduction, while nilpotent structure
can change the target Chern character and Euler characteristic.
Nothing here rules out a generically nonreduced CM target.

## 7. Provenance

- Anh Duc Vo, *Generic Vanishing for Singular Varieties via Du Bois
  complexes*, arXiv:2410.11109, especially Theorems 4.3 and 6.1,
  Proposition 8.4/Theorem B, Proposition 9.1, and Example 9.2(2).
- M. Popa and C. Schnell, generic vanishing for mixed Hodge modules on
  abelian varieties, cited by Vo as the input to Theorem 6.1.
- A. Ogus and H. Dao--S. Takagi for zero local-cohomological defect of
  Cohen--Macaulay surfaces and threefolds, as cited in Vo Example
  9.2(2).
- Kovacs--Schwede injectivity for the dual Du Bois morphism, used in
  Vo's nonnegativity argument.

This is a research-bank reduction, not a solution of the Hodge
conjecture and not a Clay theorem.
