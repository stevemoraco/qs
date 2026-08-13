# A locally Atiyah-safe complete-intersection branch and its negative-Ext firewall

**Date:** 2026-08-13  
**Status:** exact positive local algebra with an exact global twist; not a viable
Markman/Perry deformation object because the split virtual representative is
not gluable  
**Scope:** codimension-two complete intersections and the transverse-node
K-class. Local vanishing is proved; global semiregularity is not.

## 1. The local rank-one module

Let \(R\) be a smooth local \(\mathbf C\)-algebra and let
\(I=(x,y)\) be a regular-sequence ideal. Put
\[
 u=\binom{x}{y},\qquad v=(x,y),\qquad
 B=uv=\begin{pmatrix}x^2&xy\\xy&y^2\end{pmatrix},
 \qquad A=\binom{-y}{x}. \tag{1}
\]
Since \(u:R\to R^2\) is injective,
\[
 \ker B=\ker v=\operatorname{im}A.
\]
Thus, for \(N=\operatorname{coker}B\),
\[
 0\longrightarrow R\xrightarrow{A}R^2
 \xrightarrow{B}R^2\longrightarrow N\longrightarrow0
 \tag{2}
\]
is exact.

The image of \(B\) is \(uI\subset uR\). Quotienting first by \(uI\)
and then by \(uR\) gives
\[
 0\longrightarrow uR/uI\longrightarrow N
 \longrightarrow R^2/uR\longrightarrow0.
\]
Here \(uR/uI\simeq R/I\), while
\[
 R^2/uR\xrightarrow{\sim}I,\qquad
 [(a,b)]\longmapsto -ya+xb.
\]
Consequently
\[
 \boxed{0\longrightarrow R/I\longrightarrow N
 \longrightarrow I\longrightarrow0,}
 \qquad
 [R/I]=[N]-[I]. \tag{3}
\]
The split derived object
\[
 Q_I=N\oplus I[1] \tag{4}
\]
therefore has the K-class of \(R/I\).

## 2. Exact local Atiyah-square nullhomotopy

With the trivial connections on (2), the raw degree-two Atiyah block on
\(\partial_x\wedge\partial_y\) is
\[
 B_xA_y-B_yA_x
 =\binom{-3x}{-3y}. \tag{5}
\]
Let
\[
 V=\begin{pmatrix}0&-3\\3&0\end{pmatrix}.
\]
Then
\[
 B_xA_y-B_yA_x=VA. \tag{6}
\]
Thus (5) is an explicit homotopy boundary. More generally, for an arbitrary
local bivector \(\pi\), the block is
\[
 -3\,\iota_\pi(dx\wedge dy)\,u,
\]
and (6) applies after multiplying \(V\) by
\(\iota_\pi(dx\wedge dy)\). Bivectors with no \(x\wedge y\)
component give zero directly. The factor \(1/2\) in the Atiyah
exponential only rescales the homotopy.

The ideal \(I\) has projective dimension one, so its local degree-two
Atiyah block is vacuous. Hence every local bivector acts trivially on the
split object (4). This is a genuine positive local model: the K-class of a
complete-intersection branch has been represented by a complex whose local
bivector Atiyah square vanishes.

## 3. Exact global twist

Let \(X\) be smooth, let \(s\in H^0(X,L_1)\) and
\(t\in H^0(X,L_2)\) be a regular sequence, and let
\(Z=V(s,t)\). Define
\[
 K=(L_1L_2)^{-1},\qquad
 E=L_1^{-1}\oplus L_2^{-1},\qquad
 F=L_1\oplus L_2,
\]
and
\[
 A=(-t,s):K\to E,\qquad
 B=\binom{s}{t}(s,t):E\to F. \tag{7}
\]
The types in (7) are exact:
\(t\) maps \(K\to L_1^{-1}\), \(s\) maps
\(K\to L_2^{-1}\), the row \((s,t)\) maps \(E\to\mathcal O_X\),
and the column maps \(\mathcal O_X\to F\). Moreover \(BA=0\), and
Koszul exactness gives
\[
 0\longrightarrow K\xrightarrow A E\xrightarrow B F
 \longrightarrow N\longrightarrow0. \tag{8}
\]
As locally, \(\operatorname{im}B=uI_Z\subset u\mathcal O_X\).
The quotient by \(u\mathcal O_X\) is the standard Koszul presentation of
\(I_ZL_1L_2\). Therefore
\[
 \boxed{0\longrightarrow\mathcal O_Z\longrightarrow N
 \longrightarrow I_ZL_1L_2\longrightarrow0.} \tag{9}
\]
In particular
\[
 Q_Z=N\oplus(I_ZL_1L_2)[1],
 \qquad [Q_Z]=[\mathcal O_Z]. \tag{10}
\]
For \(L_1=L_2=L\), the correct bundles are
\[
 0\to L^{-2}\to2L^{-1}\to2L\to N\to0,
 \qquad
 0\to\mathcal O_Z\to N\to I_ZL^2\to0. \tag{11}
\]
Earlier variants with an extra twist on the left term of (9) are false and
are retracted.

## 4. The transverse-crossing virtual class

For two transverse branches with ideals \(I,J\), the selected
partial-normalization stalk has K-class
\[
 [R]-[R/I]-[R/J]. \tag{12}
\]
Using one copy of (3) for each branch, the split object
\[
 R\oplus I\oplus J\oplus N_I[1]\oplus N_J[1] \tag{13}
\]
has exactly the class (12), because
\[
 [R]+[I]+[J]-[N_I]-[N_J]
 =[R]-[R/I]-[R/J].
\]
Every summand in (13) has locally trivial bivector Atiyah square. Thus (13)
removes the unit local obstruction of the separated-branch cone at the
level of a split virtual object.

## 5. Fatal scope: negative Ext and global gluing

The positive conclusion above is local and K-theoretic. It does not produce
an object to which the Markman/Perry deformation theorem applies.

First, (4) is not gluable:
\[
 \operatorname{Ext}^{-1}(Q_I,Q_I)
 \supset
 \operatorname{Hom}(N,I)\ne0, \tag{14}
\]
where the nonzero map is the canonical quotient in (3). It is also visibly
nonsimple because of its direct-sum idempotents. The crossing object (13)
has still more negative Ext; for example, its unshifted and shifted summands
give nonzero cross-Homs. Perry's semiregularity deformation theorem requires
\(\operatorname{Ext}^{<0}=0\), so (4), (10), and (13) fail before any
semiregularity calculation.

There is also an exact firewall against coupling the two summands in the
actual ample complete-intersection geometry. Put
\[
 J=I_ZL_1L_2
\]
and let \(q:N\twoheadrightarrow J\) be (9). Since \(X\) is normal and
\(J\) is rank-one torsion-free with reflexive hull \(L_1L_2\),
\[
 \mathcal End(J)=\mathcal O_X.
\]
If \(f:J\to N\), the composite \(qf\) is a global regular scalar.
The connecting map for (9) sends that scalar to the scalar multiple of the
nonzero extension class. On a connected projective \(X\), it follows that
\[
 qf=0. \tag{15}
\]
Thus every such \(f\) factors through \(\mathcal O_Z\hookrightarrow N\);
in particular it is generically zero. This factorization alone does not
imply that global negative Ext survives: a generically rank-one negative
Ext sheaf can have no global sections.

For the theta complete intersections at issue here, however, the factor is
zero. Regularity gives
\[
 I_Z/I_Z^2\simeq L_1^{-1}|_Z\oplus L_2^{-1}|_Z,
\]
hence
\[
 \operatorname{Hom}(J,\mathcal O_Z)
 \simeq
 H^0\!\left(Z,L_1^{-1}|_Z\oplus L_2^{-1}|_Z\right)=0 \tag{16}
\]
when \(L_1,L_2\) are ample and \(Z\) is a positive-dimensional reduced
complete intersection. Therefore \(f=0\) in the actual theta setup:
no internal differential \(J\to N\) can remove the split
\(\operatorname{Ext}^{-1}\) class.

Second, the homotopy (6) is a stalkwise statement. Local trivializations of
\(L_1,L_2\) need not glue the homotopies globally; line-bundle Atiyah
classes can leave a higher local-to-global component of the characteristic
action. No global vanishing of
\(\operatorname{HH}^2(X)\to\operatorname{Ext}^2(Q_Z,Q_Z)\) is claimed.

Finally, the opposite-orientation two-term complex
\[
 [N\xrightarrow{q} I_ZL_1L_2] \tag{17}
\]
is quasi-isomorphic to \(\mathcal O_Z\) by (9). It has the same K-class,
but it is not an internal differential \(J\to N\) on the graded object
(10). It kills the obvious negative-Ext defect only by returning to the
ordinary complete-intersection object and its nontrivial local
\(ds\wedge dt\) Atiyah square. Any successful repair must find a
different nonsplit architecture that simultaneously kills negative Ext,
preserves the K-class, and retains the local nullhomotopy.

## 6. A connective local boundary point that is safe but divisorial

The failure of split gluing does not mean every nonzero local coupling
restores the Atiyah-square obstruction. There is an exact positive boundary
example.

Return to \(I=(x,y)\) and (1). Let \(J_0=\left(\begin{smallmatrix}
0&-1\\1&0
\end{smallmatrix}\right)\). Multiplication by \(x^2\) on \(I\) lifts
to a map \(f:I\to N\) using
\[
 C=x^2J_0:R^2\to R^2,\qquad H=\binom{-x}{0}:R\to R^2.
\]
The identities
\[
 (-y,x)C=x^2(x,y),\qquad CA=BH
\]
verify the chain map. Since \(qf=x^2\operatorname{id}_I\), the map
\(f\) is injective. Its mapping cone is already minimal:
\[
 0\to R^2\xrightarrow{D_2}R^4\xrightarrow{D_1}R^2
 \to\operatorname{coker}f\to0, \tag{18}
\]
with
\[
 D_2=\begin{pmatrix}
 -y&-x\\x&0\\0&y\\0&-x
 \end{pmatrix},\qquad
 D_1=\begin{pmatrix}
 x^2&xy&0&-x^2\\
 xy&y^2&x^2&0
 \end{pmatrix}. \tag{19}
\]
For \(\pi=\partial_x\wedge\partial_y\), the raw Atiyah-square block is
\[
 (D_1)_x(D_2)_y-(D_1)_y(D_2)_x
 =
 \begin{pmatrix}-3x&0\\-3y&3x\end{pmatrix}
 =V D_2, \tag{20}
\]
where
\[
 V=\begin{pmatrix}
 0&-3&0&0\\3&0&0&-6
 \end{pmatrix}.
\]
All bivectors involving the other smooth parameters give zero. Hence every
local bivector block is nullhomotopic: this nonsplit connective object is
locally Atiyah-square safe.

It is not a selected-point repair. Because \(qf=x^2\operatorname{id}_I\),
its cokernel is supported along the divisor \(x=0\), not only at the
crossing point. Thus the example proves that connectivity and local safety
are compatible, but only after changing the punctured support geometry.

## 7. Claim, critic, salvage

**Claim that survives.** Equations (1)--(11) give an exact locally
Atiyah-safe virtual representative of a complete-intersection branch, with
all twists fixed.

**Fatal critic.** The split representative is neither gluable nor simple,
and stalkwise nullhomotopies do not prove global characteristic-action
vanishing.

**Best salvage.** Search the deformation space of nonsplit differentials on
the same graded bundles, imposing
\(\operatorname{Ext}^{<0}=0\) and simplicity before testing the global
trace-free action. The canonical quotient is the boundary point that
collapses back to \(\mathcal O_Z\).

No exceptional Hodge class and no Millennium theorem is proved here.
