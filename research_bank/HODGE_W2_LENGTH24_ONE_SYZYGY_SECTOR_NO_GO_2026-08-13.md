# Length-24 filtered Hilbert–Burch obstructions on \(W_2(C)\)

**Date:** 2026-08-13  
**Status:** GREEN for the additive filtered-\(K\)-theory conclusions under the
stated constant-Betti hypothesis; **not a Hodge-conjecture result**.

## 1. Scope and target

Let \(C\) be a nonhyperelliptic genus-four curve and
\(S=W_2(C)\subset J(C)\). Put
\[
X=[p+C],\quad H=\Theta|_S,\quad D=3X-H,\quad
V=N^\vee_{S/J(C)},\quad v=c_1(V).
\]
The standard data are
\[
X^2=1,\ XH=4,\ H^2=12,\ K_S=X+H,\ v=-K_S,
\]
\[
v^2=21,\quad c_2(V)=6,\quad Dv=1,\quad D^2=-3,\quad
vX=-5,\quad DX=-1.
\]
For a normally-flat homogeneous length-24 algebra
\(E=\bigoplus E_d\), the \(d=23\) target forces
\[
c_1(E)=tD,\qquad
\int_S\left(\operatorname{ch}_2(E)-\frac12c_1(E)K_S\right)=-552.
\tag{1.1}
\]
Assume the fiberwise minimal graded Betti ranks are constant.

## 2. A surviving restriction lemma

For \(j_p:C\to C^{(2)}\), \(q\mapsto p+q\), local symmetric coordinates
\(s=z_1+z_2,\ u=z_1z_2\) along \(z_1=0,z_2=z\) give
\[
ds\mapsto(1,dz),\qquad du\mapsto(z,0).
\]
Therefore
\[
0\to\Omega_S|_X\to(K_p\otimes\mathcal O_C)\oplus K_C
 \xrightarrow{(a,\omega)\mapsto a-\omega(p)}k_p\to0.
\tag{2.1}
\]
The kernel on global sections is the graph of evaluation. Restricting the
conormal sequence shows that \(V|_X\) has rank two, degree \(-5\), and no
global section. A destabilizing line \(M\subset V\) would give a globally
generated quotient \(V^\vee\to M^\vee\) of degree at most two. Degree zero
contradicts \(H^0(V)=0\), degree one is impossible on a positive-genus
curve, and degree two would give a \(g^1_2\). Hence \(V|_X\) is stable.

In characteristic zero \(\operatorname{Sym}^dV|_X\) is semistable, so every
actual quotient \(E_d\) of rank \(h_d\) satisfies
\[
\deg_XE_d\ge-\frac{5d}{2}h_d,\qquad
t\le\frac52\sum_d d\,h_d.
\tag{2.2}
\]
This inequality is retained as a constraint only; by itself it does not
eliminate all length-24 types.

## 3. The descent firewall

Let \(R=\operatorname{Sym}_S V\), \(A=R/I\), and define the canonical
coefficient sheaves
\[
B_{i,d}=\operatorname{Tor}^{R}_i(A,\mathcal O_S)_d.
\]
Constant fiber Betti ranks make these sheaves locally free and compatible
with base change, degree by degree. Local minimal graded resolutions need
not glue as direct sums: changes of local lifts may contain positive-degree
polynomial off-diagonal entries. Their free terms instead have intrinsic
degree filtrations whose associated graded pieces are
\[
R(-d)\otimes B_{i,d}.
\]
After sheafification on
\(\pi:\mathbf P(V)\to S\), with
\[
\pi_*\mathcal O(d)=\operatorname{Sym}^dV,\qquad
\xi^2-v\xi+c_2(V)=0,
\]
one still has the additive \(K\)-theory identities
\[
[F_i]=\sum_d[\pi^*B_{i,d}\otimes\mathcal O(-d)].
\tag{3.1}
\]
Consequently all additive Chern-character eliminations below survive.
Statements requiring an individual later generator bundle to inject into
\(\operatorname{Sym}^dV\) do **not** follow from constant Betti data.

### Buried overclaim

The earlier draft asserted that every later generator coefficient bundle
was a subbundle of the corresponding symmetric power and used this to
eliminate the three-generator type
\((1,2,3,4,5,5,4)\). This inference is false: on overlaps a degree-\(b\)
generator may change by polynomial multiples of earlier degree-\(a\)
generators. Equivalently, a free term can be a nonsplit filtered extension
\[
0\to R(-b)L\to F\to R(-a)G\to0.
\]
The additive \(K\)-class survives, but the separate subbundle slope bound
does not. The three-generator type is therefore **open in this note**.

## 4. Finite one-syzygy classification with at most two generator degrees

For one generator degree the numerator is
\[
1-(q+1)z^a+qz^b.
\]
The moment equations give
\(a=q\delta,\ b=(q+1)\delta\) and
\(q(q+1)\delta^2/2=24\). The unique solution is
\[
h=(1,2,3,4,5,6,3),\qquad 1-4z^6+3z^8.
\tag{4.1}
\]

For two generator degrees \((p,a),(r,b)\), with one syzygy degree \(c\)
and rank \(p+r-1\), put \(u=c-a>0,\ w=c-b>0\). Then
\[
c=pu+rw,
\]
\[
p(p-1)u^2+r(r-1)w^2+2pruw=48.
\tag{4.2}
\]
Up to swapping, the positive solutions are
\[
\begin{gathered}
(1,1;1,24),(1,1;2,12),(1,1;3,8),(1,1;4,6),\\
(1,2;1,4),(1,2;5,2),(1,3;7,1),
(1,3;2,2),(2,2;2,2).
\end{gathered}
\]
The last two have \(u=w\) and merge into the one-block type (4.1).
Thus the seven genuine two-block types are the four complete intersections
\[
(1,24),(2,12),(3,8),(4,6)
\]
and
\[
(a,b,c;r)=(8,5,9;2),(4,7,9;2),(3,9,10;3).
\tag{4.3}
\]
A finite proof uses \(p+r\le7\), \(p\le r\), followed by direct divisor
enumeration in (4.2).

There is one further one-syzygy-degree Hilbert function,
\[
(1,2,3,4,5,5,4),
\]
with three generator degrees. It is not eliminated here because of the
descent issue in Section 3.

## 5. Additive obstructions that survive

### One generator block

For (4.1), the first and only generator block is the actual ideal piece in
degree six. The degree-seven multiplication
\[
V\otimes G\longrightarrow\operatorname{Sym}^7V
\]
is an isomorphism. Its determinant gives \(2c_1(G)=24v\), and the finite
quotient class gives
\[
c_1(E)=44v.
\]
Its Gysin image is nonzero, contradicting \(c_1(E)\in\mathbf QD\).

### Complete intersections

The curvilinear type \((1,24)\) is excluded by
\[
(2m-1)u^2-u=4,\qquad m=24.
\]
The homogeneous-CI GRR/resultant calculation excludes
\((2,12),(3,8),(4,6)\): the first two force incompatible integral
Néron–Severi congruences, while the last forces
\[
171n^2+496n-20403=0,
\]
whose discriminant \(14201668\) lies strictly between \(3768^2\) and
\(3769^2\).

### Three non-CI two-block types

Using only the filtered additive identities (3.1), the quotient \(K\)-class,
and (1.1), the three cases in (4.3) force
\[
\begin{array}{c|c|c}
(a,b,c;r)&\text{equation}&\text{discriminant}\\ \hline
(4,7,9;2)&t^2+48t-21248=0&87296\\
(8,5,9;2)&t^2+27t-13412=0&54377\\
(3,9,10;3)&t^2+87t-42392=0&177137.
\end{array}
\]
The discriminants lie strictly between \(295^2,296^2\);
\(233^2,234^2\); and \(420^2,421^2\), respectively. Hence none admits
rational \(t\).

## 6. Corrected theorem and boundary

**Theorem.** No normally-flat homogeneous length-24 thickening supported on
\(W_2(C)\), in a constant minimal-Betti stratum with one syzygy degree and
at most two generator degrees, has the \(d=23\) theta-secant character.

There are exactly two length-24 Hilbert functions whose generators occur
in one degree. The type (4.1) is excluded above. The other is
\[
h=(1,2,3,4,5,6,2,1),
\]
and its filtered projective Hilbert–Burch calculation gives
\[
3t^2+67t-33138=0,\qquad
\Delta=402145,\qquad 634^2<\Delta<635^2.
\]
Thus every one-generator-degree type is eliminated.

The result does not cover the remaining one-syzygy type with three
generator degrees, Betti jumping, non-normally-flat thickenings, or the
remaining length-24 types having at least two syzygy degrees. It also does
not verify the independent 16-class semiregularity gate.

## Provenance

The graded quotient spaces are treated by A. Iarrobino and J. Yaméogo,
*The family \(G_T\) of graded quotients of \(k[x,y]\) of given Hilbert
function*, arXiv:alg-geom/9709021v2. Betti strata are treated by
A. Iarrobino, *Betti strata of height two ideals*,
arXiv:math/0407364v2. Symmetric-power semistability in characteristic zero
is the standard Ramanan–Ramanathan theorem. The \(C^{(2)}\) intersection
data are classical Macdonald/Poincaré formulas.

This is a finite-sector obstruction, not a proof of the Hodge conjecture.
The global argument has not been formalized in Lean.
