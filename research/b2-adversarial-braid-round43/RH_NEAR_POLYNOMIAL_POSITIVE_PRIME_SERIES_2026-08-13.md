# Riemann hypothesis — near-polynomially damped ordinary-prime positive series

Date: 2026-08-13 UTC

Branch: `automation/b2-round43-rh-subpolynomial-positive-weight-20260813`

Parent theorem: `RH_SUBPOLYNOMIAL_POSITIVE_EXCESS_WEIGHT_CLASS_2026-08-13.md`.

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL,
🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE,
🚧 MISSING.

**Status:** 🟢 PROVED human analytic corollary; 🧩 exact arithmetic
discretization of the near-polynomial positive-excess criterion; 🔵 finite
ordered-field spine on this branch and an independently banked finite Bregman
spine in `RH-Lean`; **NOT RH. FIVE-ALARM OFF.**

## 1. Statement

For `p>=17`, put

\[
e(p)=\vartheta(p)-p
\]

and

\[
L_*(p)=p^{-1/\log\log p}.
\]

Define the ordinary-prime series

\[
\mathcal S_*
=
\sum_{p\ge17}
\frac{[\vartheta(p)-p]_+\log p}
{p^{\,3/2+1/\log\log p}}.
\tag{1.1}
\]

### Theorem RH-43C

\[
\boxed{
\mathrm{RH}
\iff
\mathcal S_*<\infty.
}
\tag{1.2}
\]

## 2. Convex staircase decomposition

Let

\[
F(y)=\frac12(y_+)^2
\]

and

\[
w(x)=x^{-3/2-1/\log\log x}
\qquad(x\ge17).
\]

The function `w` is positive, continuously differentiable, and decreasing.
At a prime `p`, the Chebyshev state has jump

\[
e(p)-e(p^-)=\log p.
\]

Define the endpoint Bregman residual

\[
B_p
=e(p)_+\log p-
\left[F(e(p))-F(e(p^-))\right].
\tag{2.1}
\]

Convexity gives `B_p>=0`. The exact Stieltjes chain rule and integration by
parts, on `[17,X]` with a fixed endpoint convention, give

\[
\begin{aligned}
\sum_{17\le p\le X}w(p)e(p)_+\log p
={}&
\int_{17}^{X}w(x)e_+(x)dx\\
&+w(X)F(e(X))-w(17)F(e(17))\\
&+\int_{17}^{X}[-w'(x)]F(e(x))dx\\
&+\sum_{17\le p\le X}w(p)B_p.
\end{aligned}
\tag{2.2}
\]

All terms except the fixed lower-endpoint constant are nonnegative. Therefore

\[
\boxed{
\mathcal S_*(X)
\ge
\int_{17}^{X}
\frac{e_+(x)}{x^{\,3/2+1/\log\log x}}dx
-C_0,
}
\tag{2.3}
\]

where `C_0=w(17)F(e(17))` is finite. In fact `e(17)<0`, so with the natural
right-continuous convention `C_0=0`; the finite constant is retained in (2.3)
to make the endpoint scope robust.

Equation (2.2) is the same convex/Stieltjes identity independently derived in
the banked Round-252 Bregman proof; only the weight has changed.

## 3. False RH implies divergence

Theorem RH-43B on this branch proves that false RH forces

\[
\int_{17}^{\infty}
\frac{e_+(x)}{x^{\,3/2+1/\log\log x}}dx
=\infty.
\]

Equation (2.3) therefore gives

\[
\mathcal S_*=\infty.
\]

No prime-arrival threshold, next-prime estimate, or conversion from a
subsequence to a full limit is used: the series has nonnegative terms, and its
partial sums dominate an unbounded nonnegative integral up to one fixed
constant.

## 4. RH implies convergence

Under RH,

\[
e(p)_+\ll p^{1/2}(\log p)^2,
\]

so the summand in (1.1) is

\[
\ll
\frac{L_*(p)(\log p)^3}{p}.
\tag{4.1}
\]

Partition the primes into logarithmic blocks

\[
e^n\le p<e^{n+1}.
\]

On such a block,

\[
L_*(p)\le L_*(e^n)=e^{-n/\log n},
\]

`log p<=n+1`, and `1/p<=e^{-n}`. The elementary Chebyshev upper bound gives

\[
\pi(e^{n+1})\ll\frac{e^{n+1}}{n}.
\]

Hence the total contribution of the block is

\[
\ll n^2e^{-n/\log n}.
\tag{4.2}
\]

The series

\[
\sum_n n^2e^{-n/\log n}
\]

converges; for large `n`, `n/log n>=sqrt n`, so it is dominated by
`n^2e^{-sqrt n}`. This proves convergence of (1.1) under RH.

Together with Section 3, this proves Theorem RH-43C. ∎

## 5. Strength relative to the logarithmic series

The previously banked ordinary-prime criterion used, for fixed `k>2`,

\[
\sum_p
\frac{[\vartheta(p)-p]_+}
{p^{3/2}(\log p)^k}.
\]

The new summand contains

\[
p^{-1/\log\log p}\log p,
\]

which decays faster than every fixed negative power of `log p`. Yet it remains
larger than `p^{-epsilon}` for every fixed `epsilon>0`, so a zero at horizontal
excess `delta>0` still produces a polynomial spike that outruns the damping.

Thus the ordinary-prime route admits damping arbitrarily close to a fixed
power without losing equivalence to RH.

## 6. Claim + counterexample + best salvage

### Claim killed

The positive ordinary-prime series is terminal only near the logarithmic
threshold `k>2`, so logarithmic mass may be the main obstruction.

### Countertheorem

The same exact positive series remains terminal after replacing the logarithmic
weight by the much smaller `p^{-1/log log p}` factor.

### Best salvage

Attack (1.1), not a weaker logarithmically damped series, when testing a
one-sided prime-distribution mechanism. Failure at (1.1) demonstrates a power-
scale obstruction rather than a poor logarithmic budget.

## 7. Hostile critic

1. The series criterion is an RH equivalent, not an unconditional estimate.
2. The Bregman decomposition is exact but does not bound any positive bank.
3. A fixed extra power `p^{-epsilon}` would no longer detect zeros with
   horizontal excess below `epsilon`; the vanishing exponent is load-bearing.
4. The block proof uses only a classical upper bound for the number of primes;
   it does not import unproved prime randomness.
5. The finite Lean files do not formalize Stieltjes integration, prime blocks,
   asymptotics, or the equivalence to RH.

### Critic verdict

🟢 SURVIVES at human analytic level.

🧩 The simplest current arithmetic positive target is the series (1.1).

🚧 MISSING — prove its convergence unconditionally, which is exactly RH.

## 8. Formal status

- 🔵 LEAN-SOURCE / ✅ after branch replay: the finite endpoint-extraction and
  exponent-margin spine in
  `verification/b2-round43/RHSubpolynomialPositiveWeightFinite.lean`.
- Independently banked finite Bregman spine:
  `stevemoraco/RH-Lean@fc90c4111b3e0a03c768f82e308c395001a4c69c`,
  `Millennium/RH/ChebyshevPositiveBregmanFinite.lean`.
- 🚧 No end-to-end Lean theorem about primes or RH.

## 9. Provenance

- Continuous weight theorem on this branch:
  `RH_SUBPOLYNOMIAL_POSITIVE_EXCESS_WEIGHT_CLASS_2026-08-13.md`.
- Parent positive decomposition:
  `stevemoraco/RH@af6690e73cc88ef9a42f0e90158bd402341a0b82`.
- Primary false-RH spike source: Daniel R. Johnston, arXiv:2201.06184v2,
  Theorem 1.4 and Section 5.

**FIVE-ALARM OFF.**
