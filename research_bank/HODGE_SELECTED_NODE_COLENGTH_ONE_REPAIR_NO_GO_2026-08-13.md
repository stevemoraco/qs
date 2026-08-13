# The smallest K-preserving selected-node repair still has rank-five Atiyah square

**Date:** 2026-08-13  
**Status:** exact local no-go for both colength-one orbits; research only  
**Scope:** the completed transverse-node ring
\(R=\mathbf C[[u,v,w,z]]\), its separated-branch object, and the
smallest replacement by one rank-one module. This does not classify larger
finite-length corrections or arbitrary derived replacements.

## 1. The K-preserving repair problem

Put
\[
 I=(u,v),\qquad J=(w,z),\qquad N=IJ
   =(uw,uz,vw,vz),\qquad k=R/\mathfrak m.
\]
For the separated crossing there is an exact sequence
\[
 0\longrightarrow R/(IJ)\longrightarrow R/I\oplus R/J
 \longrightarrow k\longrightarrow0. \tag{1}
\]
Consequently the cochain object \([R\to R/I\oplus R/J]\), in degrees
\(0,1\), has K-class
\[
 [N]-[k]. \tag{2}
\]
The smallest way to replace its two cohomology modules by one rank-one
module without changing (2) is to choose a nonzero functional
\[
 \lambda:N/\mathfrak mN\longrightarrow k
\]
and set
\[
 M_\lambda=\ker(N\twoheadrightarrow k). \tag{3}
\]
Then \([M_\lambda]=[N]-[k]\).

The action of \(\operatorname{GL}(I/\mathfrak mI)\times
\operatorname{GL}(J/\mathfrak mJ)\) on
\[
 N/\mathfrak mN\simeq
 (I/\mathfrak mI)\otimes(J/\mathfrak mJ)
\]
has exactly two nonzero functional orbits, of matrix rank one and rank two.
Thus (3) has only two local orbit types.

For the rank-one representative \(\lambda(uw)=1\), the module is the
explicit ideal
\[
 M_\lambda=(uz,vw,vz,u^2w,uw^2). \tag{4}
\]
For the rank-two representative with
\(\lambda(uw)=\lambda(vz)=1\), it is
\[
 M_\lambda=(uz,vw,uw-vz). \tag{5}
\]

## 2. Exhaustion among rank-one torsion-free single sheaves

The preceding construction is not merely a convenient family. It exhausts
the rank-one torsion-free single-sheaf repairs, provided the point correction
is interpreted in K-theory with support.

Let \(U=\operatorname{Spec}R\setminus\{\mathfrak m\}\), and suppose
\(M\) is a rank-one torsion-free \(R\)-module equipped with an isomorphism
\[
 M|_U\simeq N|_U, \tag{6}
\]
whose relative class in \(K_0^{\mathfrak m}(R)\) is
\[
 [M]-[N]=-[k]. \tag{7}
\]
Equivalently, after the punctured identification below, the correction has
point length one.

Because \(R\) is a regular local UFD, every rank-one reflexive module is
free. Moreover \(N^{**}=R\): at every height-one prime, both \(I\) and
\(J\) become the unit ideal. After identifying the two reflexive hulls
with \(R\), the isomorphism (6) is multiplication by an element
\(f\in\operatorname{Frac}(R)^*\). At every height-one prime it carries
one copy of \(R_p\) isomorphically to the other, so every valuation of
\(f\) is zero. Normality gives \(f,f^{-1}\in R\); hence \(f\) is a
unit. Rescaling by that unit makes \(M\) and \(N\) literally equal on
\(U\).

It remains to identify the saturation. The exact sequence
\[
 0\to R/IJ\to R/I\oplus R/J\to k\to0
\]
gives \(\operatorname{depth}(R/IJ)=1\), and
\[
 0\to N\to R\to R/IJ\to0
\]
then gives \(\operatorname{depth}N=2\). Therefore
\[
 H^0_{\mathfrak m}(N)=H^1_{\mathfrak m}(N)=0,
 \qquad
 N=\Gamma(U,\widetilde N). \tag{8}
\]
Since \(M|_U=N|_U\), (8) embeds \(M\subset N\), with finite-length
quotient. Dévissage in \(K_0^{\mathfrak m}(R)\simeq\mathbf Z[k]\)
and (7) give
\[
 \operatorname{length}(N/M)=1. \tag{9}
\]
Thus \(M=M_\lambda\) for a nonzero functional as in (3), and the two
matrix-rank orbits listed above are exhaustive.

The support qualifier in (7) is essential. In ordinary local \(K_0(R)\),
the class of \(k\) is zero by its Koszul resolution, so an unqualified
ordinary-K-theory equality would not determine the correction length.

## 3. A chain map that controls both orbits

Order the generators of \(N\) as
\[
 g=(uw,uz,vw,vz).
\]
A minimal resolution of \(N\) has first syzygies
\[
 \begin{aligned}
 s_1&=(-v,0,u,0),&s_2&=(0,-v,0,u),\\
 s_3&=(-z,w,0,0),&s_4&=(0,0,-z,w),
 \end{aligned}
\]
and the unique second relation
\[
 (z,-w,-v,u). \tag{6}
\]
Write
\[
 \lambda=(a,b,c,d)
\]
in the dual basis to \(g\). Lift \(N\to k(-2)\) to the Koszul
resolution of \(k(-2)\), with degree-one basis
\(e_u,e_v,e_w,e_z\). The chain map in homological degrees one and two is
\[
 \begin{aligned}
 \phi_1(s_1)&=c e_u-a e_v,&
 \phi_1(s_2)&=d e_u-b e_v,\\
 \phi_1(s_3)&=b e_w-a e_z,&
 \phi_1(s_4)&=d e_w-c e_z, \tag{7}
 \end{aligned}
\]
and
\[
 \boxed{\;
 \phi_2(\lambda)=
 a,e_v\wedge e_z-b,e_v\wedge e_w
 -c,e_u\wedge e_z+d,e_u\wedge e_w .
 \;} \tag{8}
\]
Indeed, applying the Koszul differential to (8) gives
\[
 z\phi_1(s_1)-w\phi_1(s_2)-v\phi_1(s_3)+u\phi_1(s_4),
\]
which verifies the chain-map equation. Formula (8) is nonzero for every
nonzero \(\lambda\). In particular, the degree-two Tor map is linear in
\(\lambda\); it is not the determinant of the associated \(2\times2\)
matrix and does not vanish on the rank-one orbit.

Let
\[
 V=\mathfrak m/\mathfrak m^2,\qquad
 C_\lambda=\frac{\Lambda^2V}{\mathbf C\phi_2(\lambda)}. \tag{9}
\]
Minimalizing the shifted mapping cone of the chain map leaves the same
Koszul tail in both orbits:
\[
 R(-6)\otimes\Lambda^4V
 \longrightarrow R(-5)\otimes\Lambda^3V
 \longrightarrow R(-4)\otimes C_\lambda. \tag{10}
\]
The two minimal Betti tables are
\[
\begin{array}{c|cccc}
 &F_0&F_1&F_2&F_3\\ \hline
 \operatorname{rank}(\lambda)=2&
 3R(-2)&5R(-4)&4R(-5)&R(-6)\\
 \operatorname{rank}(\lambda)=1&
 3R(-2)\oplus2R(-3)&
 2R(-3)\oplus5R(-4)&4R(-5)&R(-6).
\end{array} \tag{11}
\]
Both give the required Hilbert numerator
\[
 3t^2-5t^4+4t^5-t^6
 =
 (4t^2-4t^3+t^4)-t^2(1-t)^4. \tag{12}
\]
The degree-three pair in the rank-one table is real minimal data, not a
license to delete the common K-polynomial terms.

## 4. The rank-five Atiyah-square certificate

Choose a volume form
\[
 \mathrm{vol}=e_u\wedge e_v\wedge e_w\wedge e_z.
\]
The two differentials in the Koszul tail (10) are linear. With trivial
connections, direct contraction of their raw Atiyah square gives, up to the
nonzero universal sign/scalar determined by the convention for
\(\operatorname{At}^2\),
\[
 \Lambda^2T_R\longrightarrow C_\lambda,\qquad
 \pi\longmapsto
 \operatorname{pr}_{C_\lambda}(\iota_\pi\mathrm{vol}). \tag{13}
\]
With the convention in which both ordered wedge terms are retained, the
map is \(\pm2\operatorname{pr}_{C_\lambda}
(\iota_\pi\mathrm{vol})\). The scalar is irrelevant in characteristic
zero.

Contraction with \(\mathrm{vol}\) identifies
\(\Lambda^2T_R\) with \(\Lambda^2V\). Since (9) quotients by exactly
one nonzero vector, (13) has
\[
 \boxed{\operatorname{rank}=5.} \tag{14}
\]
This constant top block cannot be a homotopy boundary. The resolution is
minimal, so every differential has entries in \(\mathfrak m\); every
boundary in the endomorphism complex therefore vanishes after reduction
modulo \(\mathfrak m\), whereas every nonzero value of (13) survives.
Hence five independent local bivector directions give nonzero classes in
\(\operatorname{Ext}^2_R(M_\lambda,M_\lambda)\).

On an abelian fourfold, translation-invariant bivectors evaluate
surjectively onto the local bivectors. Thus a rank-five local action leaves
many global bivectors available for the same Chern-annihilator construction
used at the selected node. Neither orbit can make the bivector
characteristic action vanish identically, so neither repairs the weaker
semiregularity gate.

## 5. Claim, retracted counterclaim, and salvage

**Claim.** Both colength-one subideal orbits preserve the separated-node
K-class but retain a rank-five nonzero local Atiyah-square action.

**Retracted counterclaim.** The degree-two Tor map is not
\(\det(\lambda)\). Formula (8) is the smallest counterexample: it remains
nonzero for every rank-one \(\lambda\). Accordingly, the rank-one
Atiyah-square rank is five, not six.

**Best salvage.** Any successful repair must move beyond a colength-one
rank-one module: use a larger finite-length correction whose top Koszul
quotient can cancel more than one bivector direction, or a genuinely derived
complex with cross-cohomology cancellation. Such a construction still has
to preserve the global secant Chern character and simplicity.

No exceptional Hodge class and no Millennium theorem is proved here.
