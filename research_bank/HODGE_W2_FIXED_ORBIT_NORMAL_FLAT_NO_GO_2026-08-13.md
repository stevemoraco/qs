# Hodge theta target: fixed-orbit normally-flat \(W_2\) thickenings do not work

**Date:** 2026-08-13  
**Status:** research theorem / scoped obstruction, not a Millennium solution  
**Scope:** length-\(24\), normally-flat, homogeneous thickenings supported on a smooth \(W_2(C)\) whose graded binary Artin algebra has one fixed \(\mathrm{GL}_2\)-orbit over the support  
**Not covered:** a graded algebra moving in the relative multigraded Hilbert scheme; non-normally-flat thickenings; other supports; the full Hodge conjecture  
**Provenance:** claimant computation by the Millennium Braid loop; independent hostile reconstruction and subgroup-case repair on 2026-08-13

## 1. Numerical target

Let \(C\) be a very general nonhyperelliptic curve of genus \(4\),
\[
 S=C^{(2)}\simeq W_2(C)\hookrightarrow A=J(C),
\]
and put \(H=\Theta|_S\), \(X=[C+p]\). Then
\[
 X^2=1,\quad XH=4,\quad H^2=12,\quad K_S=X+H,\quad K_S^2=21.
\]
The conormal bundle \(V=N^*_{S/A}\) has
\[
 v:=c_1(V)=-K_S,\qquad c_2(V)=6,
\]
so
\[
 c_2(\operatorname{End}_0V)=4c_2(V)-v^2=24-21=3[\mathrm{pt}]. \tag{1}
\]

For the \(k=1\) theta target, a length-\(24\) graded algebra bundle
\(E=\operatorname{gr}\mathcal O_Z\) on \(S\) must satisfy
\[
 c_1(E)\cdot H=0,\qquad
 \int_S\left(\operatorname{ch}_2(E)-\frac12c_1(E)K_S\right)
 =24(1-24)=-552. \tag{2}
\]
The Todd term is included in (2); omitting it gives a wrong right-hand side.

## 2. Fixed-orbit hypothesis

Assume the homogeneous ideal bundle defining \(E\) is locally obtained from one
finite-colength homogeneous ideal
\(I_0\subset\operatorname{Sym}(\mathbf C^2)\) by changes of frame of \(V\).
Equivalently, the frame bundle reduces to
\[
 G=\operatorname{Stab}_{\mathrm{GL}_2}(I_0),
 \qquad
 E=P_G\times^G(\operatorname{Sym}(\mathbf C^2)/I_0).
\]
Scalars lie in \(G\); write \(\bar G\subset\mathrm{PGL}_2\) for the projective
stabilizer. This hypothesis fails when the fiber algebra moves between
\(\mathrm{GL}_2\)-orbits in the relative multigraded Hilbert scheme.

## 3. Stabilizer cases

### 3.1. \(\bar G=\mathrm{PGL}_2\)

Every homogeneous piece of \(I_0\) is \(0\) or all of
\(\operatorname{Sym}^d\mathbf C^2\), because the latter is irreducible in
characteristic zero. The ideal condition gives \(I_0=(x,y)^r\), of colength
\(r(r+1)/2\). But \(21<24<28\), so this case is impossible.

### 3.2. \(\bar G\) finite

The adjoint representation on \(\operatorname{End}_0(\mathbf C^2)\) factors
through \(\bar G\). The corresponding finite étale torsor trivializes
\(\operatorname{End}_0(V)\). If \(p:T\to S\) is that cover, then
\(p^*c_2(\operatorname{End}_0V)=0\). Finite pullback is injective rationally,
because
\[
 p_*p^*=(\deg p)\operatorname{id}.
\]
This contradicts (1).

### 3.3. \(\bar G\) contained in a Borel

A Borel preserves a line, so \(V\) has line Chern roots \(l,m\) on \(S\), with
\[
 l+m=-K_S,\qquad lm=6.
\]
For very general \(C\), \(\operatorname{NS}(S)=\mathbf ZX\oplus\mathbf ZH\).
Writing \(l=aX+bH\), the equation \(l(-K_S-l)=6\) is
\[
 a^2+8ab+12b^2+5a+16b+6=0. \tag{3}
\]
Its discriminant factorization
\[
 n^2=16b^2+16b+1,\qquad
 (4b+2-n)(4b+2+n)=3
\]
gives exactly the unordered pairs
\[
 \{l,m\}=\{-2X,X-H\}
 \quad\text{or}\quad
 \{-3X,2X-H\}. \tag{4}
\]
A \(\operatorname{Pic}^0\)-twist does not change the intersections below.

A triangular filtration of the polynomial quotient has characters
\(w=il+jm\), \(i,j\ge0\). Chern character is additive through it. A character
\(w\) contributes
\[
 R(w)=\frac12(w^2+w\,v),\qquad v=l+m=-K_S, \tag{5}
\]
to the left side of (2). For the two pairs in (4), respectively,
\[
 2R(il+jm)=4i^2+12ij+5j^2+10i+11j, \tag{6}
\]
\[
 2R(il+jm)=9i^2+12ij+15i+6j. \tag{7}
\]
Each is strictly positive unless \(i=j=0\). A length-\(24\) algebra has nonunit
weights, so (2) is impossible.

### 3.4. Positive-dimensional \(\bar G\), not contained in a Borel

The remaining algebraic subgroup of \(\mathrm{PGL}_2\) lies in the normalizer of
a torus. Its other component exchanges the two roots. On the associated étale
double cover, non-diagonal weights occur in pairs
\((il+jm,jl+im)\). No assertion about the Néron--Severi group of the cover is
needed. From \((l+m)^2=21\) and \(lm=6\),
\[
 2\{R(il+jm)+R(jl+im)\}
 =9(i^2+j^2)+24ij+21(i+j), \tag{8}
\]
positive unless \(i=j=0\). A diagonal weight \(iv\), \(i>0\), contributes
\[
 2R(iv)=21i(i+1)>0. \tag{9}
\]
Again (2) is impossible.

## 4. The scoped theorem

> **Fixed-orbit \(W_2\) obstruction.**
> Under Sections 1 and 2, no length-\(24\) normally-flat homogeneous thickening
> of \(W_2(C)\subset J(C)\) has the theta-target Chern character.

Sections 3.1--3.4 cover every projective stabilizer.

## 5. Hostile audit and exact boundary

The inference “choose a monomial ideal in each fiber and enumerate partitions”
is invalid in general. A normally-flat algebra is a section of the relative
multigraded Hilbert scheme, and its fibers need not remain in one
\(\mathrm{GL}_2\)-orbit. Without a single-orbit theorem, local monomial forms do
not reduce the frame bundle to one stabilizer. Tautological relation bundles can
acquire Chern classes in the moduli direction.

**Smallest structural warning.** A fixed monomial ideal globalizes only when the
transition functions of \(V\) reduce to its stabilizer. Having the same Hilbert
function in every fiber is insufficient.

**Best salvage.** The remaining normally-flat \(W_2\) lane must use a genuinely
moving family of binary Artin algebras, or prove that the embedding forces
isotriviality. This is the exact missing bridge.

## 6. Exact arithmetic regression

\`\`\`python
def dot(p, q):
    a, b = p
    c, d = q
    return a*c + 4*(a*d+b*c) + 12*b*d

K, v = (1, 1), (-1, -1)
assert dot(K, K) == 21
assert 4*6 - dot(v, v) == 3
assert 6*7//2 == 21 < 24 < 28 == 7*8//2

root_pairs = [
    ((-2, 0), (1, -1)),
    ((-3, 0), (2, -1)),
]
for l, m in root_pairs:
    assert (l[0]+m[0], l[1]+m[1]) == v
    assert dot(l, m) == 6

for i in range(9):
    for j in range(9):
        F1 = 4*i*i + 12*i*j + 5*j*j + 10*i + 11*j
        F2 = 9*i*i + 12*i*j + 15*i + 6*j
        Fswap = 9*(i*i+j*j) + 24*i*j + 21*(i+j)
        assert (F1 == 0) == (i == j == 0)
        assert (F2 == 0) == (i == j == 0)
        assert (Fswap == 0) == (i == j == 0)

sol = []
for a in range(-50, 51):
    for b in range(-50, 51):
        if a*a + 8*a*b + 12*b*b + 5*a + 16*b + 6 == 0:
            sol.append((a, b))
assert sorted(sol) == [(-3, 0), (-2, 0), (1, -1), (2, -1)]
\`\`\`

## 7. Literature anchor

The primitive filtration is not used here. For its distinction from general
multiple schemes, see Jean-Marc Drézet, *Primitive multiple schemes*, European
Journal of Mathematics 7 (2021), arXiv:2004.04921. Section 1 gives
\(\mathcal I_X^j/\mathcal I_X^{j+1}\simeq L^j\) in the primitive case; this note
instead treats an embedding-dimension-two normally-flat setting.
