# Riemann hypothesis — a subpolynomially damped positive Chebyshev-excess criterion

Date: 2026-08-13 UTC

Branch: `automation/b2-round43-rh-subpolynomial-positive-weight-20260813`

Parent: `stevemoraco/qs@6a425986687c9c2b99a3f18c11892fc6dadaf99d`

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL,
🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE,
🚧 MISSING.

**Status:** 🟢 PROVED human analytic weight-class theorem from a published
false-RH spike theorem and the classical RH Chebyshev estimate; 📚 SOURCE-
VERIFIED against Johnston's Theorem 1.4 and proof; 🧩 sharper RH-equivalent
positive target; 🔵 finite Lean spine staged separately; ✅ pending replay at
this commit; **NOT RH. FIVE-ALARM OFF.**

## 0. Setup

Let

\[
e(x)=\vartheta(x)-x,
\qquad e_+(x)=\max(e(x),0).
\]

Fix `x_0>=2`. Let `L:[x_0,infinity)->(0,infinity)` be nonincreasing and assume:

### RH-integrability condition

\[
\int_{x_0}^{\infty}
L(x)\frac{(\log x)^2}{x}\,dx<\infty.
\tag{0.1}
\]

### Subpolynomial lower condition

For every `alpha>0`,

\[
\lim_{x\to\infty}x^\alpha L(x)=+\infty.
\tag{0.2}
\]

Condition (0.2) says that the damping is smaller than every fixed negative
power of `x`. It is stronger and less ambiguous than writing only
`L(x)=x^{-o(1)}`.

Define

\[
\mathcal C_L
=
\int_{x_0}^{\infty}
\frac{e_+(x)L(x)}{x^{3/2}}\,dx.
\tag{0.3}
\]

## 1. Weight-class theorem

### Theorem RH-43A

Under (0.1), (0.2), positivity, and monotonicity of `L`,

\[
\boxed{
\mathrm{RH}
\iff
\mathcal C_L<\infty.
}
\tag{1.1}
\]

### Proof: RH implies convergence

Under RH, the classical von Koch/Chebyshev estimate is

\[
|\vartheta(x)-x|
=O\!\left(x^{1/2}(\log x)^2\right).
\tag{1.2}
\]

Therefore

\[
0\le
\frac{e_+(x)L(x)}{x^{3/2}}
\ll
L(x)\frac{(\log x)^2}{x}.
\]

Condition (0.1) proves convergence.

### Proof: false RH implies divergence

Put

\[
\omega=\sup\{\Re\rho:\zeta(\rho)=0\},
\qquad
\delta=\omega-\frac12.
\]

If RH is false, functional-equation symmetry gives `delta>0`.

Johnston's Theorem 1.4 and its proof, specialized to the Chebyshev integral
and `c=3/2`, imply that for every `eta` with `0<eta<delta` there are arbitrarily
large `X` such that

\[
J(X):=
\int_{x_0}^{X}
\frac{e(x)}{x^{3/2}}\,dx
\ge c_\eta X^{\delta-\eta}
\tag{1.3}
\]

for some `c_eta>0`. Changing the fixed lower endpoint from `2` to `x_0`
changes the integral by a constant and does not alter the polynomial positive
spikes.

Since `L` is positive and nonincreasing, for `x_0<=x<=X` one has
`L(x)>=L(X)`. Also `e_+>=e`. Hence

\[
\begin{aligned}
\int_{x_0}^{X}
\frac{e_+(x)L(x)}{x^{3/2}}\,dx
&\ge
L(X)
\int_{x_0}^{X}
\frac{e_+(x)}{x^{3/2}}\,dx\\
&\ge L(X)J(X).
\end{aligned}
\tag{1.4}
\]

Along the spike sequence, (0.2) with `alpha=delta-eta` gives

\[
L(X)X^{\delta-\eta}\to\infty.
\]

Thus the partial integrals in (0.3) are unbounded, and the nonnegative
integral diverges. This proves (1.1). ∎

## 2. Explicit near-polynomial damping

Take

\[
x_0=e^e,
\qquad
L_*(x)=x^{-1/\log\log x}
=
\exp\!\left(-\frac{\log x}{\log\log x}\right).
\tag{2.1}
\]

### Monotonicity

Write `t=log x`. The exponent `t/log t` has derivative

\[
\frac{\log t-1}{(\log t)^2}>0
\qquad(t>e).
\]

Therefore `L_*` is decreasing on `(e^e,infinity)`.

### Subpolynomial lower condition

For every `alpha>0`,

\[
x^\alpha L_*(x)
=
\exp\!\left(
(\log x)\left[\alpha-\frac1{\log\log x}\right]
\right)
\to\infty.
\tag{2.2}
\]

### RH integrability

With `t=log x`, condition (0.1) becomes

\[
\int_e^\infty
 t^2\exp\!\left(-\frac{t}{\log t}\right)dt.
\tag{2.3}
\]

For all sufficiently large `t`, `log t<=sqrt t`, so
`t/log t>=sqrt t`. The tail in (2.3) is bounded by

\[
\int^\infty t^2e^{-\sqrt t}dt<\infty.
\]

Thus `L_*` satisfies every hypothesis of Theorem RH-43A.

### Corollary RH-43B

\[
\boxed{
\mathrm{RH}
\iff
\int_{e^e}^{\infty}
\frac{[\vartheta(x)-x]_+}
{x^{\,3/2+1/\log\log x}}\,dx
<\infty.
}
\tag{2.4}
\]

This is a much more strongly damped target than the previously banked
`(log x)^{-4}` positive-excess integral. The extra exponent still tends to
zero, so every fixed off-critical zero produces a polynomial spike that
outruns the damping.

## 3. General logarithmic-coordinate form

Let `Phi:[log x_0,infinity)->[0,infinity)` be nondecreasing and put

\[
L(x)=e^{-\Phi(\log x)}.
\]

Sufficient conditions for Theorem RH-43A are

\[
\Phi(t)=o(t)
\tag{3.1}
\]

and

\[
\int_{\log x_0}^{\infty}t^2e^{-\Phi(t)}dt<\infty.
\tag{3.2}
\]

Condition (3.1) gives (0.2); condition (3.2) is exactly (0.1) after
`x=e^t`; monotonicity of `Phi` gives monotonicity of `L`.

Examples include

\[
\Phi(t)=t^a\quad(0<a<1),
\]

and, for large `t`,

\[
\Phi(t)=\frac{t}{\log t}.
\]

Thus there is a continuum of positive RH equivalents ranging from logarithmic
damping to damping arbitrarily close, on the exponent scale, to a fixed power.

## 4. Claim + counterexample + best salvage

### Claim killed

The logarithmic weight `(log x)^{-4}` is a load-bearing or nearly maximal
feature of the positive Chebyshev-excess criterion.

### Countertheorem

The proof needs only RH-integrability and survival of every fixed polynomial
false-RH spike. Every weight satisfying (0.1)--(0.2) gives an equivalent, and
`x^{-1/log log x}` is much smaller than any negative power of `log x`.

### Best salvage

Use the strongly damped criterion (2.4) when testing analytic or arithmetic
upper-bound mechanisms. Any method that still fails at (2.4) is not being
blocked by a gratuitously weak logarithmic weight.

## 5. Hostile critic

1. This theorem does not bound (2.4); that bound is exactly equivalent to RH.
2. The positive-part operation is nonlinear. Classical PNT errors remain far
   too large: multiplying a near-`x` unconditional error by a subpolynomial
   damping cannot manufacture the square-root power saving.
3. Condition (0.2) is essential. A fixed extra power `x^{-epsilon}` can erase
   off-line zeros with horizontal excess below `epsilon` and is not terminal
   for RH.
4. Monotonicity is used at the exact endpoint-extraction step (1.4). Without
   it, a weight may be tiny precisely on Johnston's spike sequence.
5. The proof inherits Johnston's `Omega_+` theorem and the classical RH
   Chebyshev estimate; neither is formalized end-to-end in the companion Lean
   file.
6. No novelty claim is made without a specialist literature search for
   positive-part weighted Chebyshev criteria.

### Critic verdict

🟢 SURVIVES with the stated hypotheses.

🧩 The strongest simple positive target is now the near-polynomially damped
integral (2.4), not the logarithmically damped predecessor.

🚧 The missing theorem remains an unconditional one-sided square-root-scale
prime-distribution estimate.

## 6. Formal status

The companion Lean source formalizes only:

- finite endpoint extraction for a nonincreasing positive weight;
- domination of signed mass by positive-part mass;
- the scalar exponent-margin arithmetic used after the subpolynomial factor is
  below half a fixed off-line exponent.

It does not define `theta`, zeta zeros, integrals, asymptotics, or RH.

## 7. Provenance

- Newest audited parent criterion:
  `stevemoraco/RH@af6690e73cc88ef9a42f0e90158bd402341a0b82`.
- Primary analytic source: Daniel R. Johnston, *On the average value of
  pi(t)-li(t)*, arXiv:2201.06184v2; Canadian Mathematical Bulletin 66 (2023),
  Theorem 1.4 and Section 5.
- Source audit: Theorem 1.4 allows `c=3/2`; its proof gives the exponent
  `omega-1/2-eta` for arbitrarily large positive Chebyshev weighted-integral
  spikes.
- The exact B52 dyadic-prime positive-part target remains separately banked at
  `stevemoraco/RH@c231c5986f5db181ee3ded6200ef5340d1461a4f`.

**FIVE-ALARM OFF. This is an RH equivalent, not a proof of RH.**
