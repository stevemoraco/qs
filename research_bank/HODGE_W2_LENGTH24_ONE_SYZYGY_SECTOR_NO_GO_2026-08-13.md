# Length-24 homogeneous Hilbert–Burch obstructions on \(W_2(C)\)

**Date:** 2026-08-13  
**Status:** GREEN for the stated constant-Betti, normally-flat sector; **not a Hodge-conjecture result**.

## 1. Scope and target

Let \(C\) be a nonhyperelliptic genus-four curve and
\(S=W_2(C)\subset J(C)\). Put
\[
X=[p+C],\quad H=\Theta|_S,\quad D=3X-H,\quad
V=N^\vee_{S/J(C)},\quad v=c_1(V).
\]
The standard intersection data are
\[
X^2=1,\ XH=4,\ H^2=12,\ K_S=X+H,\ v=-K_S,
\]
\[
v^2=21,\quad c_2(V)=6,\quad Dv=1,\quad D^2=-3,\quad
vX=-5,\quad DX=-1.
\]
For a normally-flat homogeneous length-24 algebra
\(E=\bigoplus E_d\), the \(d=23\) theta-secant target forces
\[
c_1(E)=tD,\qquad
\int_S\left(\operatorname{ch}_2(E)-\frac12c_1(E)K_S\right)=-552.
\tag{1.1}
\]
We assume throughout that the fiberwise minimal Betti degrees and ranks are
constant, so their generator and syzygy coefficient sheaves are vector
bundles and commute with base change.

## 2. Restriction stability

Let \(j_p:C\to C^{(2)}\), \(q\mapsto p+q\). Near \((p,p)\in C\times C\),
choose parameters \(z_1,z_2\) and invariant coordinates
\(s=z_1+z_2,\ u=z_1z_2\). Along \(z_1=0,z_2=z\),
\[
ds\mapsto(1,dz),\qquad du\mapsto(z,0).
\]
Thus
\[
0\to\Omega_S|_{X}\to (K_p\otimes\mathcal O_C)\oplus K_C
 \xrightarrow{(a,\omega)\mapsto a-\omega(p)} k_p\to0.
\tag{2.1}
\]
The kernel on global sections is the graph of evaluation, so the ambient
invariant differentials
\(H^0(K_C)\to H^0(\Omega_S|_X)\) are an isomorphism. Restricting the
conormal sequence gives
\[
0\to V|_X\to H^0(K_C)\otimes\mathcal O_C\to\Omega_S|_X\to0,
\]
hence \(\operatorname{rk}V=2,\ \deg V=-5,\ H^0(V)=0\).

If a saturated line \(M\subset V\) destabilized \(V\), then
\(\deg M\ge-2\). Dualizing gives a globally generated line quotient
\(V^\vee\to M^\vee\) of degree at most two. Degree zero would force
\(M^\vee=\mathcal O_C\), contradicting \(H^0(V)=0\); degree one is
impossible on a positive-genus curve; degree two would give a \(g^1_2\),
contradicting nonhyperellipticity. Therefore \(V|_X\) is stable.

In characteristic zero, \(\operatorname{Sym}^dV|_X\) is semistable.
Every rank-\(h_d\) quotient \(E_d\) therefore satisfies
\[
\deg_XE_d\ge-\frac{5d}{2}h_d,
\quad\text{hence}\quad
t\le\frac52\sum_d d\,h_d.
\tag{2.2}
\]

## 3. Relative Hilbert–Burch firewall

Use the quotient-line convention
\[
\pi:\mathbf P(V)\to S,\quad \pi_*\mathcal O(d)=\operatorname{Sym}^dV,
\quad \xi^2-v\xi+c_2(V)=0.
\tag{3.1}
\]
On a constant minimal Betti stratum, relative Hilbert–Burch gives
\[
0\to\bigoplus_j\pi^*Q_j\otimes\mathcal O(-b_j)
 \to\bigoplus_i\pi^*G_i\otimes\mathcal O(-a_i)
 \to\mathcal O\to0.
\tag{3.2}
\]
Expanding its Chern character in
\(\mathrm{CH}^*(\mathbf P(V))_\mathbf Q\) gives intrinsic relations among
the coefficient bundles. No splitting of \(V\), monomial normal form, or
fixed-orbit hypothesis is used.

## 4. Finite one-syzygy-degree classification

### One generator degree

A numerator
\[
1-(q+1)z^a+qz^b
\]
satisfies \(a=q\delta,\ b=(q+1)\delta\), and colength 24 gives
\[
\frac{q(q+1)\delta^2}{2}=24.
\]
The unique solution is \((q,\delta)=(3,2)\):
\[
h=(1,2,3,4,5,6,3),\qquad P=1-4z^6+3z^8.
\tag{4.1}
\]

### Two generator degrees

Let the generator ranks/degrees be \((p,a),(r,b)\), and let the sole
syzygy block have rank \(p+r-1\) and degree \(c\). Set
\(u=c-a>0,\ w=c-b>0\). The first two Hilbert moments give
\[
c=pu+rw,
\]
\[
p(p-1)u^2+r(r-1)w^2+2pruw=48.
\tag{4.2}
\]
Up to swapping, the nine positive solutions of (4.2) are
\[
\begin{gathered}
(1,1;1,24),(1,1;2,12),(1,1;3,8),(1,1;4,6),\\
(1,2;1,4),(1,2;5,2),(1,3;7,1),
(1,3;2,2),(2,2;2,2).
\end{gathered}
\]
The last two have \(u=w\), so their generator degrees merge and both give
(4.1). Thus there are seven genuine two-block types: four complete
intersections \((1,24),(2,12),(3,8),(4,6)\), and
\[
(a,b,c;r)=(8,5,9;2),(4,7,9;2),(3,9,10;3).
\tag{4.3}
\]
A direct finite proof of the list follows from \(p+r\le7\), \(p\le r\),
and solving
\(rw((r-1)w+2u)=48\) for \(p=1\), followed by \(p=2,3\).

### Three generator degrees

There is one additional length-24 numerator with syzygies in one degree:
\[
h=(1,2,3,4,5,5,4),\quad
P=1-z^5-z^6-3z^7+4z^8.
\tag{4.4}
\]
Consequently exactly nine of the 122 length-24 Hilbert functions have all
minimal syzygies in one degree.

## 5. Obstructions

### The one-block type

For (4.1), relative Hilbert–Burch is
\[
0\to Q\mathcal O(-8)\to G\mathcal O(-6)\to\mathcal O\to0,
\quad \operatorname{rk}(Q,G)=(3,4).
\]
The degree-seven multiplication \(V\otimes G\to\operatorname{Sym}^7V\)
is an isomorphism. Determinants give \(2c_1(G)=24v\), while the quotient
class gives
\[
c_1(E)=44v.
\]
Its Gysin image is nonzero, contradicting \(c_1(E)\in\mathbf QD\).

### Complete intersections

The curvilinear type \((1,24)\) is excluded by the primitive-multiple
equation
\[
(2m-1)u^2-u=4,\qquad m=24.
\]
The types \((2,12),(3,8),(4,6)\) are excluded by the independently
derived homogeneous-complete-intersection GRR/resultant calculation:
the first two have incompatible integral Néron–Severi congruences, while
the last forces
\[
171n^2+496n-20403=0,
\]
whose discriminant \(14201668\) lies strictly between \(3768^2\) and
\(3769^2\).

### Three non-CI two-block types

Expanding (3.2), computing the finite quotient \(K\)-class, and applying
(1.1) gives respectively:
\[
\begin{array}{c|c|c}
(a,b,c;r)&\text{forced equation}&\text{discriminant}\\ \hline
(4,7,9;2)&t^2+48t-21248=0&87296\\
(8,5,9;2)&t^2+27t-13412=0&54377\\
(3,9,10;3)&t^2+87t-42392=0&177137.
\end{array}
\]
These discriminants lie strictly between \(295^2,296^2\);
\(233^2,234^2\); and \(420^2,421^2\), respectively. None is a square,
so none admits rational \(t\).

### The three-generator type

For (4.4), let \(A,B,G\) be the degree \(5,6,7\) generator bundles of
ranks \(1,1,3\). There are no syzygies through degree seven and
\(E_7=0\), so
\[
A\otimes\operatorname{Sym}^2V\oplus B\otimes V\oplus G
 \simeq \operatorname{Sym}^7V.
\tag{5.1}
\]
Writing \(a,b,g\) for first Chern classes gives
\[
3a+2b+g=24v,\qquad c_1(E)=55v-3a-b=tD,
\]
hence \(g=-31v-b+tD\). On \(X\),
\[
\deg G=155-\deg B-t.
\]
The intrinsic injections
\(B\hookrightarrow\operatorname{Sym}^6V\) and
\(G\hookrightarrow\operatorname{Sym}^7V\), together with Section 2,
give
\[
\deg B\le-15,\qquad \deg G\le-53,
\]
so \(t\ge223\). But
\(\sum d h_d=89\), and (2.2) gives
\[
t\le\frac{445}{2}=222.5,
\]
a contradiction.

## 6. Sector theorem and boundary

**Theorem.** No normally-flat homogeneous length-24 thickening supported on
\(W_2(C)\), lying in a constant relative minimal-Betti stratum whose
syzygies occur in one degree, has the \(d=23\) theta-secant Chern character.

The two length-24 types whose generators occur in one degree are
\((1,2,3,4,5,6,3)\) and
\((1,2,3,4,5,6,2,1)\). The first is eliminated above. For the second,
the two-syzygy-block projective-Hilbert–Burch calculation yields
\[
3t^2+67t-33138=0,\qquad
\Delta=402145,\quad 634^2<\Delta<635^2,
\]
so it too is impossible. Thus every type with generator degrees
concentrated in one degree is also eliminated.

This does **not** pass from normally flat to arbitrary thickenings, does
not cover Betti jumping, and does not cover the remaining Hilbert functions
with at least two generator degrees and at least two syzygy degrees. It also
does not verify the separate 16-class Hochschild/semiregularity gate.

## Provenance

The parameter spaces and cellular description of graded quotients are in
A. Iarrobino and J. Yaméogo, *The family \(G_T\) of graded quotients of
\(k[x,y]\) of given Hilbert function*, arXiv:alg-geom/9709021v2. Betti
strata are treated in A. Iarrobino, *Betti strata of height two ideals*,
arXiv:math/0407364v2. Symmetric-power semistability in characteristic zero
is the standard Ramanan–Ramanathan theorem. The \(C^{(2)}\) intersection
data are classical Macdonald/Poincaré formulas.

This is an independently derived finite-sector obstruction, not a proof of
the Hodge conjecture. The global argument has not been formalized in Lean.
