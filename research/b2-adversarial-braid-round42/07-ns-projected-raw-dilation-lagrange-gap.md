# Navier–Stokes — constrained Ekeland stationarity does not transfer to the raw dilation

Date: 2026-08-13 UTC

Branch: `automation/b2-round42-repsat-optimal-linear-sketch-20260813`

Exact parent: `stevemoraco/qs@64e9be6194f57e76d952e123d434d15801ee8203`

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 📚 SOURCE-VERIFIED against arXiv:2605.01875v2, Lemma 3.8 and Proposition 3.13; 🟢 PROVED an exact one-dimensional compact countermodel; 🔴 REFUTED the inference from constrained Ekeland stationarity plus Gram invertibility to the projected-to-raw dilation identity; 🧱 the strict full-Dirichlet bridge needs an independent theorem annihilating the normal Lagrange-multiplier contribution. 🔵 LEAN-SOURCE staged separately; ✅ LEAN-VERIFIED pending replay. **NOT A NAVIER--STOKES SOLUTION OR DISPROOF. FIVE-ALARM OFF.**

## 0. Source inference

The Part I manuscript fixes canonical center, scale, amplitude, and affine-frame constraints. Its admissible projected dilation `Z_perp G` is tangent to those constraints, while the raw lifted dilation

\[
Z_0G=\frac52G+X\cdot\nabla_5G
\]

is not.

For an Ekeland near-extremizer of

\[
\kappa_n\mathcal T_{G,\chi}-\Lambda_0\mathcal V_\chi,
\]

Lemma 3.8 asserts

\[
D(\kappa_n\mathcal T-\Lambda_0\mathcal V)[G_n](Z_0G_n)
=
D(\kappa_n\mathcal T-\Lambda_0\mathcal V)[G_n](Z_\perp G_n)+o(1).
\tag{0.1}
\]

The proof says the difference is a finite linear combination of constraint gradients and that uniform Gram invertibility makes its contribution only the Ekeland error.

Proposition 3.13 then combines `(0.1)` with the raw homogeneities

\[
D\mathcal T(Z_0G)=\frac32\mathcal T+o(1),
\qquad
D\mathcal V(Z_0G)=2\mathcal V+o(1),
\]

and the value relation

\[
\kappa_n\mathcal T=\Lambda_0\mathcal V+o(1)
\]

to derive `-Lambda_0/2=o(1)` and hence the strict bridge.

The missing point is elementary: constrained stationarity controls tangent derivatives. The derivative in a normal constraint direction is the Lagrange multiplier, not the Ekeland error.

---

# CLAIMANT

## 1. Exact compact countermodel

Take the ambient manifold

\[
X=(0,\infty),
\]

the fixed scale constraint

\[
m(x)=x-1=0,
\]

and the admissible class

\[
\mathcal A=\{1\}.
\]

This class is compact and complete. Its tangent space is zero.

Define

\[
\mathcal T(x)=x^{3/2},
\qquad
\mathcal V(x)=x^2,
\qquad
\Lambda_0=1,
\qquad
\kappa=1.
\]

At the unique admissible point,

\[
\mathcal T(1)=\mathcal V(1)=1,
\]

so the source's value/amplitude identity holds exactly:

\[
\kappa\mathcal T(1)=\Lambda_0\mathcal V(1).
\tag{1.1}
\]

Let the raw dilation vector be

\[
Z_0(1)=1.
\]

The constraint gradient is `m'(1)=1`; its Gram matrix is `[1]`, uniformly invertible. Orthogonal projection onto the tangent space gives

\[
Z_\perp(1)=0.
\]

Because the admissible class is a singleton, Ekeland constrained stationarity on every tangent direction holds exactly.

The raw homogeneity identities also hold exactly:

\[
D\mathcal T(1)[Z_0]
=\frac32\mathcal T(1),
\qquad
D\mathcal V(1)[Z_0]
=2\mathcal V(1).
\tag{1.2}
\]

Nevertheless

\[
\begin{aligned}
D(\mathcal T-\Lambda_0\mathcal V)(1)[Z_0]
&=\frac32-2\\
&=-\frac12,
\end{aligned}
\tag{1.3}
\]

whereas

\[
D(\mathcal T-\Lambda_0\mathcal V)(1)[Z_\perp]=0.
\tag{1.4}
\]

Thus the projected-to-raw identity `(0.1)` fails by the fixed amount `1/2`, despite:

- compactness and completeness;
- exact attainment of the quotient;
- exact constrained stationarity;
- exact value identity;
- exact `3/2` and `2` raw homogeneities;
- an invertible constraint Gram matrix;
- no leakage, tail, low-frequency, or localization error at all.

## 2. The missing normal multiplier

At a constrained extremum, the differential has the form

\[
D(\kappa\mathcal T-\Lambda_0\mathcal V)
=
\sum_j\lambda_jDm_j
+
\text{small tangent error}.
\tag{2.1}
\]

If

\[
Z_0-Z_\perp
\]

is a normal combination of constraint gradients, then `(2.1)` gives

\[
D(\kappa\mathcal T-\Lambda_0\mathcal V)(Z_0-Z_\perp)
=
\sum_j\lambda_jDm_j(Z_0-Z_\perp)
+
\text{small error}.
\tag{2.2}
\]

Gram invertibility only controls the coefficients of the normal projection. It does not show that the multipliers `lambda_j` vanish.

In the scalar model, the scale multiplier is exactly `-1/2`.

## 3. The value identity is not a multiplier identity

The paper calls

\[
\kappa_n\mathcal T=\Lambda_0\mathcal V+o(1)
\]

an amplitude identity. On the normalized class `V=1`, it is simply the near-maximizing value relation.

It does not identify the Lagrange multiplier of the scale or amplitude constraint. For ordinary amplitude scaling `G->cG`, transfer is cubic and visibility is quadratic; the multiplier selected by amplitude differentiation would carry the degree ratio `3/2`, not the value ratio `1`.

For spatial dilation, the same logical issue remains: fixing scale makes raw dilation a normal direction, so its derivative is not controlled by tangent Ekeland stationarity.

---

# CRITIC

## 4. Exact scope

The countermodel does not prove that the particular PDE multiplier is nonzero. It proves that Lemma 3.8's displayed hypotheses and proof do not imply it is zero.

A source-specific repair could establish cancellation of every normal multiplier by additional identities. But the manuscript provides no equation solving for the scale, amplitude, center, affine-frame, and parity multipliers and no reason their pairing with the raw dilation is `o(1)`.

### Critic verdict

🔴 **REFUTED AS PROVED:**

\[
\text{constrained Ekeland stationarity}
+
\text{invertible Gram matrix}
\Longrightarrow
\text{raw-dilation stationarity}.
\]

The one-dimensional singleton constraint model is an exact counterexample.

🧱 **STRICT BRIDGE BLOCKED:** Proposition 3.13 explicitly lists projected-to-raw dilation as a load-bearing input. Without `(0.1)`, the homogeneity mismatch `3/2 != 2` produces a normal Lagrange multiplier, not a contradiction.

## 5. Relation to the other Part I failures

This obstruction is independent of:

- the wrong source scaling exponent;
- the non-invariant `R^{-2}` source norm;
- the omitted bulk five-dimensional transport divergence.

Even after repairing the local PDE and scaling, the variational strictness argument would still need the missing multiplier theorem.

---

# REBUILDER

## 6. Minimum repair

A valid strict-bridge proof must do one of the following.

### A. Compute all normal multipliers

Derive the full constrained Euler--Lagrange system and prove

\[
\sum_j\lambda_jDm_j(Z_0)=o(1).
\]

The scale and amplitude multipliers cannot be discarded by Gram invertibility alone.

### B. Optimize on a dilation-invariant class

Remove the fixed scale constraint and optimize a genuinely scale-invariant quotient for which raw dilation is tangent. Then prove compactness modulo scale without reintroducing a normal direction.

### C. Build an admissible curve with raw-dilation derivative

Construct an exact constraint-preserving curve whose initial derivative has the same `T` and `V` Pohozaev pairings as the raw dilation. Projection in a Hilbert norm is insufficient; the pairings themselves must be preserved.

### 🚧 Exact remaining gap

- explicit normal multiplier equations;
- an admissible dilation theorem preserving the two Pohozaev pairings;
- a corrected strict full-Dirichlet bridge;
- all preceding local-PDE and scaling repairs;
- the axisymmetric and full-dimensional global regularity theorems.

---

## 7. Lean status

A companion finite Lean file formalizes the abstract scalar data:

\[
T=V=1,
\quad
DT(Z_0)=3/2,
\quad
DV(Z_0)=2,
\quad
Z_\perp=0,
\]

and the exact projected-to-raw discrepancy `-1/2`.

It does not formalize Ekeland's principle, Banach manifolds, constraint gradients, Pohozaev identities, or Navier--Stokes.

## 8. Provenance

Primary source checked directly:

- arXiv:2605.01875v2, Definition 3.3, Lemmas 3.7--3.9, Proposition 3.13, and Theorems 3.14--3.17;
- current source date: 5 May 2026.

Exact repository parent: `stevemoraco/qs@64e9be6194f57e76d952e123d434d15801ee8203`.

**FIVE-ALARM OFF.**
