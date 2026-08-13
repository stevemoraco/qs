# Retained transverse gluing: local Atiyah rank four and a scoped BMY firewall

**Date:** 2026-08-13  
**Status:** two exact architecture obstructions; research only  
**Scope:** one retained transverse gluing at a selected crossing, and smooth
regular zero surfaces of two specific twists of the rank-two theta bundle.

## 1. The retained-gluing local module

Let
\[
 R=\mathbf C[[x,y,z,w]],qquad I=(x,y),qquad J=(z,w).
\]
The kernel of the natural surjection
\[
 R^2\twoheadrightarrow R/(I\cap J)
\]
splits as \(R\oplus IJ\). Thus only the product ideal \(IJ\) contributes
to the degree-two local characteristic action. A minimal resolution is
\[
 R\xrightarrow{d_2}R^4\xrightarrow{d_1}R^4\longrightarrow IJ\to0,
 \tag{1}
\]
where
\[
 d_2=\begin{pmatrix}-y\\x\\w\\-z\end{pmatrix},qquad
 d_1=\begin{pmatrix}
 -w&0&-y&0\\
 z&0&0&-y\\
 0&-w&x&0\\
 0&z&0&x
 \end{pmatrix}. \tag{2}
\]
Direct multiplication gives \(d_1d_2=0\).

With trivial connections, contract the raw Atiyah-square block
\(dd_1\wedge dd_2\). In the ordered basis of the source \(R^4\), the
six coordinate bivectors give
\[
 \begin{array}{c|c}
 \pi&\iota_\pi(dd_1\wedge dd_2)\\ \hline
 \partial_x\wedge\partial_y&0\\
 \partial_z\wedge\partial_w&0\\
 \partial_x\wedge\partial_z&(0,0,0,-2)\\
 \partial_x\wedge\partial_w&(0,0,2,0)\\
 \partial_y\wedge\partial_z&(0,2,0,0)\\
 \partial_y\wedge\partial_w&(-2,0,0,0).
 \end{array} \tag{3}
\]
All differentials are minimal, so every homotopy boundary vanishes modulo
the maximal ideal. The four constant rows in (3) are independent and
nonboundaries. Hence the local bivector action has exactly
\[
 \boxed{\operatorname{rank}=4.} \tag{4}
\]

Separating the two branches instead gives the product of their individual
normalization kernels, locally \(I\oplus J\), whose summands have
projective dimension one and no degree-two local block. Therefore retaining
one gluing point is precisely what introduces the mixed four-dimensional
unit obstruction. A point-length correction may fix a K-class, but it is
not invisible to the trace-free characteristic action.

## 2. Smooth regular-zero surface firewall

Let \((X,L)\) be a principally polarized abelian fourfold, and suppose a
rank-two bundle \(Q\) has
\[
 c_1(Q)=-x,qquad c_2(Q)=6x^2,qquad x=c_1(L).
\]
Assume a saturated map
\[
 L^r\hookrightarrow Q
\]
is a regular section of
\[
 E_r=Q\otimes L^{-r}
\]
with smooth surface zero locus \(W\). Put
\[
 m=-1-2r,qquad n=r^2+r+6.
\]
Then
\[
 c_1(E_r)=mx,qquad c_2(E_r)=nx^2,qquad [W]=nx^2. \tag{5}
\]
Adjunction and the trivial tangent bundle of \(X\) give
\[
 K_W=mx|_W,
\]
and the tangent-normal sequence gives
\[
 K_W^2=24nm^2,qquad
 c_2(W)=24n(m^2-n). \tag{6}
\]

For \(r=-1\), one gets
\[
 (m,n)=(1,6),qquad K_W^2=144,qquad c_2(W)=-720,
\]
which is impossible already because the topological Euler number of a
smooth minimal surface of general type cannot satisfy BMY:
\[
 K_W^2\le3c_2(W).
\]

For \(r=-2\), one gets
\[
 (m,n)=(3,8),qquad K_W^2=1728,qquad c_2(W)=192,
\]
so \(K_W^2=9c_2(W)>3c_2(W)\), again contradicting
Bogomolov--Miyaoka--Yau. Here \(K_W=mx|_W\) is ample for both
\(r=-1,-2\), hence \(W\) is minimal of general type and BMY applies.

Equivalently, substituting (6) into BMY gives
\[
 m^2\le3(m^2-n)
 \quad\Longleftrightarrow\quad
 5r^2+5r-16\ge0, \tag{7}
\]
which fails for \(r=-1,-2\).

This theorem is deliberately scoped. For \(r=0,1\), the canonical class
is anti-ample, so BMY is not available in this orientation; no conclusion
about those twists is made here. Singular or nonregular zero schemes also
lie outside the statement.

## 3. Claim, critic, salvage

**Claim.** A retained transverse gluing carries a rank-four local
Atiyah-square obstruction, and smooth regular zero surfaces from the
\(r=-1,-2\) twists of \(Q\) are numerically impossible.

**Critic.** Neither theorem treats singular curve-defect reflexive sheaves:
minimality of the local product resolution and smoothness of the BMY surface
are essential.

**Best salvage.** Any retained-gluing construction must cancel the four
mixed local directions by genuinely derived cross-terms. For the rank-two
bundle lane, move from smooth regular zero surfaces to the explicitly
identified curve-singular reflexive frontier and recompute the
characteristic action there.

No exceptional Hodge class and no Millennium theorem is proved here.
