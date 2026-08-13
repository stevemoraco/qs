# Relative graded Tor and the \(K\)-theory firewall

**Date:** 2026-08-13  
**Status:** exact descent theorem plus counterexample; research infrastructure, not a Millennium solution  
**Use:** separates Chern-character calculations that descend canonically from assertions requiring globally split minimal generators  
**Provenance:** hostile reconstruction in the Millennium Braid research loop, 2026-08-13

## 1. Setup and conventions

Let \(S\) be reduced, \(V\) a rank-two vector bundle, and
\(A=\operatorname{Sym}_{\mathcal O_S}V\). Let
\(E=\bigoplus_{d\geq0}E_d\) be a finite graded \(A\)-algebra with
\(E_0=\mathcal O_S\), each \(E_d\) finite locally free. Define
\[
 B_{i,d}:=\operatorname{Tor}^{A}_i(E,\mathcal O_S)_d,\qquad
 \mathcal O_S=A/A_{>0}.
\]
These are the degree-\(d\) homology sheaves of the finite Koszul complex
\[
 E\otimes[\mathcal O_S\leftarrow V\leftarrow\det V].
\]

Work on a **constant full Betti stratum**: all fiber dimensions of every
\(B_{i,d}\) are locally constant. On a reduced base, a matrix of vector bundles
with constant fiber rank has locally split image and kernel: invert a maximal
minor, perform row/column operations, and use reducedness to make the larger
minors vanish. Applied degreewise, this proves every \(B_{i,d}\) finite locally
free and base-change compatible. Stacks Project Tag 05P1, Lemmas 28.21.2--3,
records the finite-locally-free criteria used here; it is not being cited for a
stronger relative-resolution statement.

For binary Artin quotients put \(G_d=B_{1,d}\), \(Q_d=B_{2,d}\).

## 2. Canonical identities

Euler characteristic of the Koszul complex gives, in \(K_0(S)[z]\),
\[
 \boxed{E(z)(1-[V]z+[\det V]z^2)
 =1-\sum_d[G_d]z^d+\sum_d[Q_d]z^d.}\tag{1}
\]
No generators, lifts, or relative minimal resolution are chosen.

Use the quotient convention
\[
 \pi:\mathbf P(V)=\operatorname{Proj}_S\operatorname{Sym}V\to S,\qquad
 \pi_*\mathcal O(d)=\operatorname{Sym}^dV.
\]
The universal quotient has Koszul relation
\[
 1-[\pi^*V\otimes\mathcal O(-1)]
 +[\pi^*\det V\otimes\mathcal O(-2)]=0
 \quad\text{in }K_0(\mathbf P(V)).\tag{2}
\]
Applying \([F]z^d\mapsto[\pi^*F\otimes\mathcal O(-d)]\) to (1) yields
\[
 \boxed{1-\sum_d[\pi^*G_d\mathcal O(-d)]
 +\sum_d[\pi^*Q_d\mathcal O(-d)]=0.}\tag{3}
\]
Thus all identities obtained by applying Chern character to (1) or (3), with
\[
 \xi^2-c_1(V)\xi+c_2(V)=0,
\]
are canonical. Coefficient extraction from (1) canonically gives each
\([E_d]\), so truncated Hilbert-series computations of \(\operatorname{ch}(E)\)
also survive. Stacks Project Tag 0B37, Section 17.26, is the exact formalism used:
short exact sequences give \(K_0\) relations and determinant is a homomorphism
from \(K_0\) of vector bundles to \(\operatorname{Pic}\).

## 3. What the identities do not prove

Constant Betti numbers do not themselves produce a globally split exact complex
\[
 0\to\bigoplus_d\pi^*Q_d\mathcal O(-d)
 \to\bigoplus_d\pi^*G_d\mathcal O(-d)
 \to\mathcal O\to0.\tag{4}
\]
Local homogeneous minimal bases may change by upper-triangular matrices with
positive-degree polynomial off-diagonal entries. These preserve internal degree
after shifts. Therefore a later \(G_d\) need not inject into
\(\operatorname{Sym}^dV\), need not have a global polynomial lift, and cannot be
given a subbundle slope bound without extra structure. A global filtered perfect
resolution may exist in a particular family, but it is extra input and is not
needed for (1)--(3). Sheafification does not turn (3) into (4).

## 4. Small explicit counterexample

Let \(S=\mathbf P^1\), \(V=\mathcal O^{\oplus2}\), with Euler sequence
\[
 0\to R=\mathcal O(-1)\to V\to W=\mathcal O(1)\to0.\tag{5}
\]
Define \(E=\mathcal O\oplus W\), \(W^2=0\), through
\(\operatorname{Sym}V\to\operatorname{Sym}W/(W^2)\). Every fiber is
\(\kappa(s)[r,w]/(r,w^2)\), a degree-\((1,2)\) complete intersection. Intrinsic
Tor bundles are
\[
 G_1=R,\qquad G_2=W^2=\mathcal O(2),\qquad Q_3=RW^2=\mathcal O(1).\tag{6}
\]
Identity (1) reads
\[
 (1+[W]z)(1-[V]z+[\det V]z^2)
 =1-[R]z-[W^2]z^2+[RW^2]z^3.\tag{7}
\]
But
\[
 \operatorname{Hom}(W^2,\operatorname{Sym}^2V)
 =H^0(\mathbf P^1,\mathcal O(-2))^{\oplus3}=0.\tag{8}
\]
Thus the later generator has no nonzero global lift into
\(\operatorname{Sym}^2V\). Fiberwise complements do not descend.

\`\`\`python
from collections import Counter
coeff = [
    Counter({(0, 0): 1}),
    Counter({(1, 0): -1}),
    Counter({(0, 2): -1}),
    Counter({(1, 2): 1}),
]
# (1+Wz)(1-(R+W)z+RWz^2)=1-Rz-W^2z^2+RW^2z^3
assert coeff[0][(0,0)] == 1
assert coeff[1][(1,0)] == -1
assert coeff[2][(0,2)] == -1
assert coeff[3][(1,2)] == 1
assert max(-2 + 1, 0) == 0  # H^0(P1,O(-2))
\`\`\`

## 5. Audit ledger

Survives without a split relative resolution:

1. GRR constraints for rank-\(24k\) graded algebras on \(W_2\);
2. primitive line-power and standard ideal-power obstructions;
3. the fixed-orbit normally-flat obstruction;
4. homogeneous complete-intersection Chern/resultant-class equations, read from
   (1)--(3);
5. the numerator \(1-4z^6+3z^8\) determinant/\(\operatorname{ch}_3\) obstruction;
6. the three intrinsic two-generator-degree/one-syzygy-degree nonsquare
   obstructions, which use only (1)--(3) and coefficient extraction;
7. their finite Diophantine degree-block enumeration;
8. the conormal splitting obstruction and restriction stability lemma.

Withdrawn unless a compatible split-lift hypothesis is proved:

1. the \(h=(1,2,3,4,5,5,4)\) slope obstruction;
2. the \(h=(1,2,3,4,5,5,3,1)\) slope obstruction;
3. the general separated-degree deficit lemma.

The counterexample is to the descent step in those proofs, not to the Hodge
target. Conditionally, if the later generators admit compatible injections into
\(\operatorname{Sym}^dV\), their recorded slope inequalities apply.

## 6. Next boundary

If Betti numbers jump, the \(B_{i,d}\) are coherent Tor sheaves rather than
vector bundles. Euler identity (1) remains valid in \(G_0(S)[z]\), but determinant
and Chern calculations acquire classes supported on the jump locus. Those
corrections must be derived rather than discarded.
