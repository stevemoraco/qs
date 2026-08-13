# The v23 theta monad: exact K identity and defect obstruction

**Date:** 2026-08-13  
**Status:** exact obstruction for one theta-line architecture, with a local
Atiyah-square firewall; research only  
**Scope:** a ppav fourfold \((X,L)\), \(x=c_1(L)\), and the \(d=23\)
target. Arbitrary vector-bundle complexes or complexes with several
cohomology sheaves are not excluded.

## 1. Exact K identity and degree convention

Through degree eight,
\[
 \boxed{v_{23}=-3e^{-x}+6e^x-3e^{5x}+e^{7x}.}\tag{1}
\]
Thus the natural complex is centered in degree zero:
\[
 3L^{-1}\xrightarrow{A}6L\oplus L^7\xrightarrow{B}3L^5,
 \tag{2}
\]
in degrees \(-1,0,1\). Its K-class is \(-,+,-\), and its Euler rank is
\(-3+7-3=1\). Putting the same bundles in degrees \([-2,-1,0]\) negates
(1) and gives Euler rank \(-1\); shifting or dualizing must be explicit.

Expanding the right side of (1) gives
\[
 1+x-\frac{23}{2}x^2-\frac{23}{6}x^3+\frac{529}{24}x^4.
\]
No adjacent two-term truncation has rank one.

## 2. Forced shape

Since
\[
 \operatorname{Hom}(L^7,L^5)=H^0(L^{-2})=0,
\]
write
\[
 B=[B_1,0],\quad B_1:6L\to3L^5,\qquad
 A=(A_1,A_7),
\]
where \(A_1:3L^{-1}\to6L\), \(A_7:3L^{-1}\to L^7\), and the complex
condition is
\[
 B_1A_1=0. \tag{3}
\]
The \(A_7\) term need not vanish, so the complex need not split.

## 3. No true monad

If \(B_1\) were everywhere surjective, \(K=\ker B_1\) would be a
rank-three bundle with
\[
 c(K)=\frac{(1+x)^6}{(1+5x)^3}. \tag{4}
\]
Expansion gives
\[
 c_1=-9x,\quad c_2=75x^2,\quad c_3=-555x^3,\quad
 \boxed{c_4=3840x^4}. \tag{5}
\]
But \(c_4\) of a rank-three bundle is zero, and
\(\int_Xx^4=24\). Hence \(B_1\) cannot be everywhere surjective. The
complex (2) cannot be a true monad exact at both ends with locally free
rank-one middle cohomology.

Equivalently,
\[
 c_4(3L^5-6L)=111x^4. \tag{6}
\]
For a transverse general \(B_1\), Thom--Porteous predicts a rank-drop
zero-cycle of length \(111\cdot24=2664\). This is a generic prediction;
(5) is the unconditional obstruction to everywhere surjective \(B_1\).

## 4. Divisorial-defect dichotomy

Let \(Q=\operatorname{coker}B_1\), and let \(D\ge0\) be its divisorial
Fitting class. Off codimension two,
\[
 \det K\simeq L^{-9}\otimes\mathcal O_X(D). \tag{7}
\]

If \(D=0\) and \(A_1\) had generic rank three, its determinant would be a
nonzero section of
\[
 \det K\otimes(\det3L^{-1})^{-1}\simeq L^{-6},
\]
impossible. Thus \(\operatorname{rank}_{gen}A_1\le2\). If the full \(A\)
is generically injective, the rank is two. Let \(T=\ker A_1\) be the
saturated generic kernel line. A nonzero map \(T\to3L^{-1}\) makes
\[
 M=L^{-1}T^{-1}\simeq\mathcal O_X(E)
\]
for an effective \(E\), after reflexive extension across codimension
two. The restriction \(A_7|_T\) is a section of
\[
 L^7T^{-1}=L^8M.
\]
If nonzero, its zero divisor has class \(8x+E\), which is nonzero; there
the full \(A\) drops rank. If it is zero, \(A\) already fails generic
injectivity. Hence the first differential has a divisorial defect.

Conversely, if \(A_1\) has generic rank three, its determinant is a
section of
\[
 \mathcal O_X(D)\otimes L^{-6},
\]
so \(D-6x\) is effective. Then \(B_1\) has a divisorial cokernel defect.

Therefore either \(A\) or \(B\) has a divisorial defect. The architecture
cannot have a torsion-free rank-one sheaf as its sole middle cohomology
with both outer cohomologies supported in codimension at least two. It
may still exist as a genuinely derived complex whose additional
cohomology carries part of (1).

The saturated/reflexive extension and generic injectivity assumptions
above are part of the theorem. No claim is made for a nonsaturated
chosen kernel before taking its reflexive hull.

## 5. Generic syzygies are absent

Equation (3) asks for three \(L^2\)-valued syzygies of \(B_1\). The
global-section map is
\[
 H^0(6L^2)\to H^0(3L^6). \tag{8}
\]
For a principal polarization on a fourfold, \(h^0(L^n)=n^4\), so the
dimensions are \(96\) and \(3888\). Explicit block maps with pairs of
\(L^4\) sections having no common divisor make (8) injective, and
injectivity is open. Thus a general \(B_1\) has no \(L^2\) syzygy. This
is not a no-go, but shows that (3) is a special incidence condition.

## 6. Local Atiyah-square firewall

Let
\[
 R^a\xrightarrow{A}R^b\xrightarrow{B}R^c,\quad BA=0,
 \quad A,B\in\mathfrak m
 \tag{9}
\]
be a minimal complex over a smooth local ring. With trivial connections,
the raw \((-2\to0)\) block of \(\operatorname{At}^2\) is
\[
 dB\wedge dA. \tag{10}
\]
The factor \(1/2\) belongs to the exponential/Chern normalization, not
the raw square, and is irrelevant to vanishing.

For a bivector \(\pi\), \(C_\pi=\iota_\pi(dB\wedge dA)\) is nullhomotopic
exactly when
\[
 C_\pi=BU+VA \tag{11}
\]
for \(U:R^a\to R^b\), \(V:R^b\to R^c\). There are no hidden degree
blocks; higher terms of \(U,V\) do not alter reduction modulo
\(\mathfrak m\).

Write \(A=\sum x_iA_i+O(\mathfrak m^2)\) and
\(B=\sum x_iB_i+O(\mathfrak m^2)\). Nullity for all coordinate
bivectors gives
\[
 B_iA_j-B_jA_i=0. \tag{12}
\]
The quadratic term of \(BA=0\) gives
\[
 B_iA_i=0,\qquad B_iA_j+B_jA_i=0. \tag{13}
\]
In characteristic zero,
\[
 B_iA_j=0\quad\forall i,j. \tag{14}
\]
This conclusion requires nullity for a spanning set of bivectors, not
one selected \(\pi\). Its strongest immediate meaning is
\[
 \sum_i\operatorname{im}A_i\subseteq\bigcap_j\ker B_j. \tag{15}
\]
It is a tangent-cone separation statement, not a grade obstruction.

For (2), the block is \(dB_1\wedge dA_1\); \(A_7\) is invisible. Where a
kernel line maps isomorphically to \(L^7\), canceling that contractible
pair leaves a two-term complex and makes the degree-two local action
vacuous. Any nontrivial class in this presentation is forced toward the
defect locus.

## 7. Exact countermodel to a grade inference

Over \(R=k[[x,y,z,w]]\), put
\[
 A=\binom{-y^2}{x},\qquad
 B=\binom{x}{y}\begin{pmatrix}x&y^2\end{pmatrix}
 =\begin{pmatrix}x^2&xy^2\\xy&y^3\end{pmatrix}. \tag{16}
\]
Then \(BA=0\), \(A\) is injective, and
\[
 \ker B=\operatorname{im}A.
\]
Indeed, \(\ker(x,y)=0\), so \(\ker B=\ker(x,y^2)\). The cokernel of \(B\)
has generic rank one and a codimension-two CM torsion piece
\(R/(x,y^2)\). The ranks \(1\to2\to2\) have Euler rank one. Since \(B\)
has order two, all \(B_i\) vanish and (14) holds.

The simpler Koszul complete intersection
\[
 R\xrightarrow{(-y^2,x)^T}R^2\xrightarrow{(x,y^2)}R
\]
also has grade two and passes the first-jet test. Thus (14) does not
force splitting or contradict codimension-two CM support. A pd-one CM
ideal minimalizes to a two-term local resolution, so its local
\(\operatorname{At}^2\) block is vacuous.

## 8. Nonsplit rank-two-minus-line obstruction

The following strengthens the split-line search and uses no Néron--Severi
rank assumption.

Suppose a rank-two vector bundle \(F\) and a line bundle \(Q\) satisfy
\[
 [F]-[Q]=v_{23}. \tag{17}
\]
Write \(q=c_1(Q)\). From
\(\operatorname{ch}(F)=v_{23}+e^q\), Newton's identities give
\[
 \begin{aligned}
 c_1(F)&=q+x,\\
 c_2(F)&=qx+12x^2,\\
 c_3(F)&=4x^2(3q+x).
 \end{aligned} \tag{18}
\]
An actual rank-two bundle has \(c_3(F)=0\). Hard Lefschetz makes
\[
 x^2\smile-:H^2(X,\mathbf Q)\longrightarrow H^6(X,\mathbf Q)
\]
an isomorphism, so (18) would force \(3q=-x\). This is impossible for
integral \(q\): the principal polarization class \(x\) is not divisible
by three. For example, \(x=3y\) with integral \(y\) would make
\(\int_Xx^4\) divisible by \(81\), whereas \(\int_Xx^4=24\).

Therefore (17) is impossible even when \(F\) is nonsplit. The sign is
essential: for a complex in degrees \((-2,-1,0)\), cancellation to
\([K]-[E]+[F]=[F]-[Q]\) must be checked before applying this theorem.

## 9. Five theta-line arithmetic obstruction

There are no integers \(a,b,c,d,k\) such that
\[
 e^{cx}+e^{dx}+e^{kx}-e^{ax}-e^{bx}=v_{23}
 \quad\text{in }\mathbf Q[x]/(x^5). \tag{19}
\]
This is a pure split K-theory obstruction; it assumes neither positivity
nor the existence of maps.

The power moments of \(v_{23}\) are
\[
 (p_0,p_1,p_2,p_3,p_4)=(1,1,-23,-23,529),
\]
so Newton's identities give
\[
 c(v_{23})=1+x+12x^2+4x^3-68x^4. \tag{20}
\]
Multiplying (20) by \((1+ax)(1+bx)\) must produce
\((1+cx)(1+dx)(1+kx)\), which has degree three. Its \(x^4\)
coefficient therefore gives
\[
 -68+4(a+b)+12ab=0,
 \qquad (3a+1)(3b+1)=52. \tag{21}
\]
Up to exchanging \(a,b\), the only integer possibilities are
\[
 (a,b)=(0,17),\quad(-1,-9),\quad(1,4). \tag{22}
\]
The remaining elementary symmetric functions of \(c,d,k\) are
\[
 c+d+k=1+a+b,\quad
 cd+ck+dk=12+a+b+ab,\quad
 cdk=4+12(a+b)+ab. \tag{23}
\]
Thus \(c,d,k\) would be the three integer roots of, respectively,
\[
 \begin{array}{c|c}
 (a,b)&\text{cubic}\\ \hline
 (0,17)&z^3-18z^2+29z-208,\\
 (-1,-9)&z^3+9z^2+11z+107,\\
 (1,4)&z^3-6z^2+21z-68.
 \end{array} \tag{24}
\]
The first two reduce modulo three to \(z^3+2z+2\), which has no root in
\(\mathbf F_3\); the third has no root in \(\mathbf F_5\).
Consequently none can have even one integer root, proving (19).

## 10. Surviving result and next bridge

**Survives:** (1) is exact, but the natural theta-line monad cannot be
true and cannot have a torsion-free sole middle cohomology without a
divisorial defect.

**Counterexample:** (16) destroys any inference from first-jet vanishing
alone to splitting or low grade.

**Best salvage:** retain the forced defect and calculate its global
trace-free characteristic action. Positivity says where the extra
cohomology must live; the local formula says where the action can
survive after generic cancellation. Simplicity and exact cancellation in
\(\operatorname{Ext}^2\) remain open.

No exceptional Hodge class and no Millennium theorem is proved here.
