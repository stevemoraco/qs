# Hodge W2-normalization Chern-character and Cohen--Macaulay no-go

**Date:** 2026-08-13  
**Status:** GREEN finite K-theoretic and depth obstruction; architecture-specific only.  
**Millennium status:** no Hodge-conjecture result.

Let \(C\) be a nonhyperelliptic genus-four curve, let
\(A=J(C)\), let \(x=[\Theta]\), and write \(S=W_2(C)\). The standard
Poincare/Macdonald calculation gives

\[
 \operatorname{ch}(\mathcal O_S)
 =\frac12x^2-\frac13x^3+\frac18x^4. \tag{1}
\]

For \(d=23\), the desired quotient character is

\[
 q_{23}=12x^2-8x^3-20x^4. \tag{2}
\]

## Theorem 1: no reduced CM target with normalization 24 copies of W2

Let \(Z\subset A\) be a reduced pure surface whose normalization is a
disjoint union of 24 translates of \(S\):

\[
 \nu:\coprod_{i=1}^{24}(S+a_i)\longrightarrow Z.
\]

Then \(Z\) cannot be Cohen--Macaulay and satisfy
\(\operatorname{ch}(\mathcal O_Z)=q_{23}\).

### Proof

The normalization sequence is

\[
 0\to\mathcal O_Z\to\nu_*\mathcal O_{\bar Z}\to Q\to0,
 \tag{3}
\]
where \(Q\) is supported on the nonnormal locus. From (1),

\[
 \operatorname{ch}_3(\nu_*\mathcal O_{\bar Z})
 =24\left(-\frac13x^3\right)=-8x^3,
\]
which is already exactly the degree-three component of (2).
Therefore (3) forces

\[
 \operatorname{ch}_3(Q)=0. \tag{4}
\]

For any coherent sheaf supported in dimension at most one on a smooth
fourfold, \(\operatorname{ch}_3\) is the effective fundamental
one-cycle with its generic module lengths. Equation (4) therefore
forces \(Q\) to be zero-dimensional.

If \(Z\) were Cohen--Macaulay of pure dimension two, it would satisfy
Serre \(S_2\). A finite normalization that is an isomorphism in
codimension one must then be an isomorphism: equivalently, the
normalization is the \(S_2\)-hull, and an \(S_2\) scheme cannot differ
from it only at closed points. Hence \(Q=0\), making \(Z\) normal,
contrary to any nontrivial gluing. If \(Q=0\) from the outset, the
character is \(24\operatorname{ch}(\mathcal O_S)\), whose degree-four
component is \(3x^4\), not \(-20x^4\). Thus no case realizes (2).
\(\square\)

## Theorem 2: pairwise point unions cannot be CM

Suppose instead one forms a reduced union of 24 translates and arranges
that different surface components meet only at isolated points. Even
without invoking (3), no nontrivial such union is Cohen--Macaulay.

At an isolated meeting point of two or more pure surface branches, the
punctured spectrum of the local ring is disconnected. A
two-dimensional Cohen--Macaulay local ring has depth two; Hartshorne
connectedness says its punctured spectrum is connected. Contradiction.

This remains true if many pair incidences are clustered at one point:
the obstruction is depth/connectivity, not the node count.

## Claimant / critic / rebuilder

**Claimant.** Twenty-four \(W_2\) components already supply the exact
\(x^2\) and \(x^3\) terms. One may hope to tune only \(x^4\) by gluing
or partially normalizing finitely many intersection points.

**Critic.** There is no degree-three budget for a conductor curve:
any positive-dimensional normalization quotient contributes an
effective \(\operatorname{ch}_3\). A point-only quotient cannot repair
an \(S_2\)/CM surface. Equivalently, isolated branch meetings violate
punctured connectedness.

**Rebuilder.** A pure CM repair must change the architecture. It must
use at least one of:

- an irreducible component with a curve of non-Du-Bois singularities;
- generically nonreduced structure;
- normal components whose individual degree-three characters differ,
  leaving a conductor budget; or
- a nonsplit higher Hilbert--Burch construction.

The previously banked partial-normalization **complex** remains an
exact simple perfect object with the desired character, but it is not
a pure CM structure sheaf and its separated-node Atiyah-square class
proves that it fails weak semiregularity.

## Scope

This note proves no statement about arbitrary surfaces with the target
character. It only rules out the normalization architecture consisting
of 24 genus-four \(W_2\) translates, and the associated point-gluing
repair. It is an obstruction, not a Hodge class and not a Millennium
advance.
