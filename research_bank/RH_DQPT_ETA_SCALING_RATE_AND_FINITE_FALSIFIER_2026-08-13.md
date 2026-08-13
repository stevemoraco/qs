# DQPT-normalized eta sums: exact scaling-rate equivalence and finite RH falsifiers

**Date:** 2026-08-13  
**Status:** GREEN exact asymptotic reformulation and one-sided finite-certificate theorem; RED as a proof of RH.  
**Scope:** the critical strip \(0<\Re s<1\). No claim is made that an experimental finite system decides the limiting exponent uniformly.

## 1. Finite object

For
\[
s=\beta+it,\qquad 0<\beta<1,
\]
define
\[
\eta_N(s)=\sum_{n=1}^{N}(-1)^{n+1}n^{-s},
\qquad
Z_N(\beta)=\sum_{n=1}^{N}n^{-\beta},
\]
and the normalized amplitude
\[
L_N(s)=\frac{\eta_N(s)}{Z_N(\beta)}.
\]

The denominator satisfies
\[
Z_N(\beta)
 =\frac{N^{1-\beta}}{1-\beta}+O_\beta(1).
\]

For \(\Re s>0\), the alternating Dirichlet series converges and
\[
\eta(s)
 =\sum_{n\ge1}(-1)^{n+1}n^{-s}
 =(1-2^{1-s})\zeta(s).
\]
The factor \(1-2^{1-s}\) has no zeros in the open critical strip.

## 2. Exact exponent dichotomy

Define, whenever the limit exists,
\[
\mathcal E(s)
 =\lim_{N\to\infty}
   \frac{-\log|L_N(s)|}{\log N}.
\]

### Theorem 2.1

For every fixed \(s=\beta+it\) with \(0<\beta<1\),
\[
\boxed{
\mathcal E(s)=
\begin{cases}
1,&\zeta(s)=0,\\[2mm]
1-\beta,&\zeta(s)\ne0.
\end{cases}}
\]

**Proof.**

If \(\zeta(s)\ne0\), then \(\eta(s)\ne0\) and
\[
\eta_N(s)=\eta(s)+o(1).
\]
Thus
\[
|L_N(s)|
 =|\eta(s)|(1-\beta)N^{-(1-\beta)}(1+o(1)),
\]
which gives \(\mathcal E(s)=1-\beta\).

If \(\zeta(s)=0\), then \(\eta(s)=0\). The Euler transformation, or one step of the alternating-tail expansion applied to \(x^{-s}\), gives
\[
\eta_N(s)
 =\frac{(-1)^{N+1}}{2(N+1)^s}
   +O_s(N^{-\beta-1}).
\]
Consequently
\[
|L_N(s)|
 =\frac{1-\beta}{2}N^{-1}(1+o(1)),
\]
so \(\mathcal E(s)=1\). \(\square\)

### Corollary 2.2 — exact RH reformulation

RH is equivalent to:
\[
\left\{s:0<\Re s<1,\ \mathcal E(s)=1\right\}
 \subseteq
\left\{s:\Re s=\frac12\right\}.
\]

This is a reformulation, not a proof. The exceptional exponent is itself defined by an infinite-size limit.

## 3. Fatal correction to a raw-zero interpretation

For every fixed \(s\) in the open critical strip,
\[
L_N(s)\longrightarrow0.
\]
Indeed, \(\eta_N(s)\) remains bounded and converges, while
\[
Z_N(\beta)\to\infty.
\]

Therefore ordinary pointwise vanishing of the normalized finite amplitude does **not** distinguish zeta zeros: it occurs at every point of the strip. Only the decay exponent separates the two cases.

Any DQPT statement reading
\[
L_N(s)\to0\quad\Longleftrightarrow\quad\zeta(s)=0
\]
is false under this normalization.

## 4. A rigorous finite off-line-zero certificate

Let \(D\) be a closed rational rectangle compactly contained in
\[
\{0<\Re s<1\}
\]
and disjoint from the critical line. Put
\[
\sigma=\min_{s\in D}\Re s>0,
\qquad
M=\max_{s\in D}|s|.
\]

Abel summation and the bounded partial sums of \((-1)^n\) give the uniform safe bound
\[
\boxed{
|\eta(s)-\eta_N(s)|
 \le
\left(1+\frac{M}{\sigma}\right)(N+1)^{-\sigma}
\quad(s\in D).
}
\]
(The constant is deliberately conservative.)

### Theorem 4.1 — finite falsifier

Suppose certified interval arithmetic proves on \(\partial D\) that
\[
|\eta_N(s)|
 >
\left(1+\frac{M}{\sigma}\right)(N+1)^{-\sigma}
\]
and certifies that the closed curve
\[
\eta_N(\partial D)
\]
has nonzero winding number about \(0\). Then \(\zeta\) has a zero in \(D\), hence RH is false.

**Proof.** On \(\partial D\),
\[
|\eta-\eta_N|<|\eta_N|.
\]
Rouché's theorem gives the same number of zeros of \(\eta\) and \(\eta_N\) in \(D\), counted with multiplicity. The certified nonzero winding gives at least one zero. Since \(1-2^{1-s}\ne0\) in the strip, it is a zeta zero. Because \(D\) is disjoint from \(\Re s=1/2\), it is off the critical line. \(\square\)

### Completeness of the falsifier family

If an off-line zeta zero exists, choose a sufficiently small rational rectangle around it, containing no boundary zero and disjoint from the critical line. Uniform convergence of \(\eta_N\to\eta\) on that boundary eventually makes the Rouché inequality hold, and the limiting winding is the zero multiplicity. Thus some finite rectangle/precision/\(N\) certificate exists.

This semidecides RH falsity only. Under RH, the search runs forever.

## 5. A second common physics bridge does not close RH

A finite Loschmidt construction based only on the Riemann–Siegel main sum encodes an approximation
\[
Z(t)=M(t)+O(t^{-1/4})
\]
on the critical line. At a true zero, the finite main sum need not vanish: it can equal the residual error. Turning approximate zero coincidence into an exact statement requires Rouché or derivative/separation bounds. Moreover, a construction confined to \(\beta=1/2\) cannot exclude zeros with \(\beta\ne1/2\).

Thus it can be a numerical zero locator, not an RH proof.

## 6. Claim / critic / rebuilder

**Claimant.** The normalized finite partition amplitude vanishes precisely at zeta zeros.

**Critic.** It tends to zero everywhere in the strip. The correct invariant is the logarithmic decay exponent, which is exactly \(1\) at zeros and \(1-\beta\) elsewhere.

**Rebuilder.** Use certified boundary enclosures and winding numbers. This yields a complete finite falsifier family for off-line zeros, but no finite positive RH certificate.

## 7. Scope discipline

- The exponent theorem is pointwise for each fixed \(s\).
- No uniform convergence of the logarithmic exponent near zeros is asserted.
- Finite experimental precision cannot distinguish arbitrarily close competing rates without explicit error bounds.
- The falsifier is a classical complex-analytic certificate in DQPT notation.
- No RH proof, disproof, Lean replay, or axiom audit is claimed.
