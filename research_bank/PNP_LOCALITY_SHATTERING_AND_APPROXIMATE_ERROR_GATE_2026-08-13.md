# P versus NP: locality, shattering, and the exact approximation-error gate

**Date:** 2026-08-13  
**Status:** Exact finite counting theorems and an architecture-specific obstruction. No \(P\ne NP\) consequence.  
**Formal status:** Not Lean-verified.

## 1. Circuit count

Fix \(m\) Boolean inputs and a finite gate basis of size \(b\), every gate
having arity at most two. Constants are two source nodes; fan-out is
unrestricted. Let \(C(m,L)\) be the number of distinct one-output
\(m\)-input Boolean functions having circuits of at most \(L\) gates.

### Lemma 1.1

With \(M=m+L+2\),
\[
 C(m,L)\le (L+1)M(bM^2)^L. \tag{1}
\]

Topologically order a circuit with exactly \(\ell\le L\) gates. At each
gate choose its type and two ordered predecessors among at most \(M\)
nodes. Unary and nullary gates are only overcounted. Choose one output
node and sum over \(\ell\). Duplicate descriptions only strengthen the
upper bound. A circuit with \(d\) designated outputs gets the additional
factor \(M^d\).

## 2. Locality versus shattering

For a family \(\mathcal A\) of Boolean functions and a finite address set
\(T\), let \(\mathcal A|_T\) be the set of restriction patterns.

### Theorem 2.1

If every \(f\in\mathcal A\) has circuit size at most \(L\), then
\[
 |\mathcal A|_T|\le C(m,L). \tag{2}
\]
If \(\mathcal A\) shatters \(k\) fixed addresses, then
\[
 2^k\le (L+1)M(bM^2)^L, \tag{3}
\]
and hence
\[
 L=\Omega\!\left(\frac{k}{\log b+\log(m+k)}\right).
\]

For a surjective selector \(q:\{0,1\}^m\to[k]\), the payload functions
\(f_y(x)=y_{q(x)}\), \(y\in\{0,1\}^k\), shatter representatives of the
\(k\) fibers. Therefore some payload has the displayed lower bound.
Nonlinear, adaptive, and first-hit selectors do not compress arbitrary
independent payload labels.

## 3. Projection entropy

Let \(\mathcal D\) be any distribution supported on \(L\)-local truth
tables and let \(\mathcal D_T\) be its projection to \(k\) addresses.
Then
\[
 |\operatorname{supp}\mathcal D_T|\le C(m,L),\qquad
 H_0(\mathcal D_T),H_\infty(\mathcal D_T)\le\log_2C(m,L). \tag{4}
\]
Exact \(k\)-wise independence makes \(\mathcal D_T\) uniform and invokes
Theorem 2.1.

## 4. Sharp atomwise approximation

Put \(K=2^k\) and \(u=1/K\). Suppose every signed exact-pattern
conjunction is fooled additively:
\[
 |\Pr[\mathcal D_T=a]-u|\le\varepsilon
 \quad\text{for every }a\in\{0,1\}^k. \tag{5}
\]

### Theorem 4.1

The exact minimum possible support size under (5) is
\[
 R_{\min}(K,\varepsilon)=
 \begin{cases}
 K,&\varepsilon<u,\\
 \lceil1/(u+\varepsilon)\rceil,&\varepsilon\ge u.
 \end{cases} \tag{6}
\]
Consequently \(C(m,L)\ge R_{\min}\), and
\[
 H_\infty(\mathcal D_T)\ge-\log_2(2^{-k}+\varepsilon)
 =k-\log_2(1+2^k\varepsilon). \tag{7}
\]

If \(\varepsilon<u\), no atom can be missing. If
\(\varepsilon\ge u\), every positive atom has mass at most
\(u+\varepsilon\); the bound is attained by the uniform distribution on
exactly \(\lceil1/(u+\varepsilon)\rceil\) patterns. Thus the threshold is
strict: already at \(\varepsilon=2^{-k}\), support may fall to \(K/2\).

Equivalently, if \(C=C(m,L)<2^k\), some signed atom test has error
\[
 \varepsilon\ge 1/C-2^{-k}. \tag{8}
\]

If instead \(\operatorname{TV}(\mathcal D_T,U_k)\le\delta\), then the
sharp bound is
\[
 |\operatorname{supp}\mathcal D_T|\ge
 \lceil(1-\delta)2^k\rceil. \tag{9}
\]
Constant total-variation closeness is therefore much stronger than
constant separate additive error for exponentially many atoms.

## 5. Parity and collision entropy

For a distribution \(\mu\) on \(\mathbf F_2^k\), define Fourier biases
\(\beta_S=\mathbf E_\mu[(-1)^{S\cdot X}]\). If
\(|\beta_S|\le\varepsilon\) for every nonempty \(S\), Parseval gives
\[
 \chi^2(\mu\|U)=\sum_{S\ne\varnothing}\beta_S^2
 \le(2^k-1)\varepsilon^2. \tag{10}
\]
Thus
\[
 |\operatorname{supp}\mu|
 \ge\frac{2^k}{1+(2^k-1)\varepsilon^2}, \tag{11}
\]
\[
 H(\mu)\ge k-\log_2(1+(2^k-1)\varepsilon^2), \tag{12}
\]
and
\[
 \operatorname{TV}(\mu,U)\le
 \tfrac12\sqrt{2^k-1}\,\varepsilon. \tag{13}
\]

This route cannot turn inverse-polynomial parity error into exponential
support. The probabilistic method supplies \(\varepsilon\)-biased
distributions of support \(O(k/\varepsilon^2)\): sample \(R\) uniform
points and apply Hoeffding plus a union bound over all nonzero parities.
One needs exponentially small error before (11) forces cubic-scale
locality.

## 6. Cubic local-PRG interface

The CKLM/CJW local-PRG construction used in approximate-MCSP
magnification has addressed output complexity
\[
 s^{1/3}2^{O(\log^{2/3}s)}.
\]
If a proposed first-hit, nonlinear-partition, adaptive-fresh, or selector
repair exposes \(k=s^{1/3+o(1)}\) independently assignable cell labels
with \(\log m=s^{o(1)}\), Theorem 2.1 forces worst-seed addressed locality
\(s^{1/3-o(1)}\). Selector ingenuity alone therefore cannot cross the
sub-\(1/3\) gate while retaining arbitrary payload exposure.

The escape is exact and load-bearing: constant-error PRGs need not
shatter. Theorem 4.1 and the parity counterexamples show why
constant/inverse-polynomial error is too weak to restore the counting
bound. Any genuine sub-\(1/3\) construction must destroy exact payload
exposure and exact independence at the final output, not merely hide
them behind a nonlinear schedule.

## 7. Scope

Covered: arbitrary nonuniform one-output circuits over any fixed finite
fan-in-two basis, constants, all sizes through \(L\), exact shattering,
projection entropy, atomwise error, total variation, and parity bias.

Not covered: infinite bases, oracle gates, arbitrary real constants,
unbounded fan-in without a new description count, multi-output circuits
without the \(M^d\) factor, or constant-error PRGs that do not shatter.

Primary context: Cheraghchi--Kabanets--Lu--Myrisiotis, *Circuit Lower
Bounds for MCSP from Local Pseudorandom Generators*; Chen--Jin--Williams,
*Sharp Threshold Results for Computational Complexity*; and
Atserias--Müller hardness magnification for approximate MCSP.

Classification: exact finite theorem / sharp route obstruction; the
Millennium gate is off.
