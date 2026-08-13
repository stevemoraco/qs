# The v23 rank-two-to-rank-three Hilbert--Burch frontier

**Date:** 2026-08-13  
**Status:** exact Chern and Riemann--Roch reduction; semihomogeneous
architectures excluded, three non-semi-stable numerical cases remain  
**Scope:** a very general principally polarized abelian fourfold
\((X,L)\), \(x=c_1(L)\), and vector bundles
\(Q\) of rank two and \(F\) of rank three with
\([F]-[Q]=v_{23}\). The reduction to three cases assumes
\(\mu_x\)-semistability of \(Q\).

## 1. Integral Hodge coordinates

For a very general ppav, the Mumford--Tate group is the full symplectic
group. Hence
\[
 H^{2,2}(X)\cap H^4(X,\mathbf Q)=\mathbf Qx^2.
\]
In a symplectic integral basis, the divided power \(x^2/2\) is integral
and primitive. Consequently
\[
 H^{2,2}(X)\cap H^4(X,\mathbf Z)
 =\mathbf Z\frac{x^2}{2}. \tag{1}
\]
Thus an algebraic rank-two bundle can be written
\[
 c_1(Q)=a x,\qquad c_2(Q)=b\frac{x^2}{2},
 \qquad a,b\in\mathbf Z. \tag{2}
\]
Equation (1) is an integral cohomology statement. It does not assert that
the primitive class \(x^2/2\) is represented by an integral algebraic
cycle on a very general ppav; existence of \(Q\) is an additional
condition.

## 2. The rank-three top-Chern equation

The already audited virtual class has
\[
 c(v_{23})=1+x+12x^2+4x^3-68x^4. \tag{3}
\]
Since \(c(F)=c(v_{23})c(Q)\) and a rank-two bundle has no Chern classes
above \(c_2\), multiplication gives
\[
 \begin{aligned}
 c_1(F)&=(a+1)x,\\
 c_2(F)&=\frac{b+2a+24}{2}x^2,\\
 c_3(F)&=\frac{b+24a+8}{2}x^3,\\
 c_4(F)&=(-68+4a+6b)x^4.
 \end{aligned} \tag{4}
\]
An actual rank-three bundle has \(c_4(F)=0\). Since \(x^4\ne0\),
\[
 \boxed{2a+3b=34.} \tag{5}
\]
In particular \(a\equiv2\pmod3\) and \(b\) is even.

This identity is necessary for every rank-two-to-rank-three
Hilbert--Burch presentation. It uses neither stability nor genericity of the
map \(Q\to F\).

## 3. Semistable reduction

Use the convention
\[
 \Delta(E)=2\operatorname{rk}(E)c_2(E)
 -(\operatorname{rk}(E)-1)c_1(E)^2.
\]
If \(Q\) is \(\mu_x\)-semistable, Bogomolov's inequality on the
fourfold gives
\[
 0\le \Delta(Q)x^2
 =(2b-a^2)x^4. \tag{6}
\]
Substituting \(b=(34-2a)/3\) yields
\[
 3a^2+4a-68\le0. \tag{7}
\]
Together with \(a\equiv2\pmod3\), this leaves exactly
\[
 \boxed{(a,b)=(-4,14),\quad(-1,12),\quad(2,10).} \tag{8}
\]
No implication from a bare Hilbert--Burch map to semistability is being
used. Without semistability of \(Q\), equation (5) has infinitely many
integer solutions.

## 4. Exact numerical table

On an abelian variety \(\operatorname{td}(X)=1\) and
\(\int_Xx^4=24\). From (2),
\[
 \chi(Q)=a^4-2a^2b+\frac{b^2}{2},\qquad
 \chi(F)=\chi(Q)+529. \tag{9}
\]
The three cases are:
\[
\begin{array}{c|c|c|c|c|c|c|c}
a&b&c_2(F)/x^2&c_3(F)/x^3&
\Delta(Q)/x^2&\Delta(F)/x^2&\chi(Q)&\chi(F)\\ \hline
-4&14&15&-37&12&72&-94&435\\
-1&12&17&-2&23&102&49&578\\
 2&10&19&33&16&96&-14&515
\end{array} \tag{10}
\]
Every entry follows directly from (4), (9), and
\[
 \Delta(F)=6c_2(F)-2c_1(F)^2.
\]

## 5. Exact semihomogeneous no-go

A semihomogeneous vector bundle on an abelian variety has
\[
 \operatorname{ch}(E)=\operatorname{rk}(E)
 \exp\!\left(\frac{c_1(E)}{\operatorname{rk}(E)}\right)
\]
and hence \(\Delta(E)=0\). This is the classical Mukai
semihomogeneous-bundle formula; a current moduli-theoretic treatment is
Gross--Kaur--Ulirsch--Werner, *Semi-homogeneous vector bundles on abelian
varieties: moduli spaces and their tropicalization* (2026),
<https://doi.org/10.1017/S2949764726100228>.

But (10) gives
\[
 \Delta(Q)\in\{12,23,16\}x^2,qquad
 \Delta(F)\in\{72,102,96\}x^2. \tag{11}
\]
Thus neither bundle in any surviving case can be semihomogeneous. In
particular, no rank-two-to-rank-three realization built from the standard
semihomogeneous/Fourier--Mukai blocks can represent \(v_{23}\).

This is stronger than the split-line obstruction but is not a general
Hilbert--Burch no-go. Stable bundles with positive discriminant are not
excluded.

## 6. Claim, critic, salvage

**Claim.** Under semistability of \(Q\), every rank-two-to-rank-three
presentation is forced into the three rows (10), and every
semihomogeneous version is impossible.

**Critic.** Stability is an extra hypothesis, and positive-discriminant
stable bundles on abelian fourfolds are not classified by this calculation.
The existence of a map \(Q\to F\) with a pure codimension-two rank-one
cokernel remains open.

**Best salvage.** For the three rows, compute wall-crossing/nonemptiness of
the moduli spaces and the Thom--Porteous class of a general map, then impose
simplicity and the trace-free Hochschild evaluation gate before attempting
a global construction.

No exceptional Hodge class and no Millennium theorem is proved here.
