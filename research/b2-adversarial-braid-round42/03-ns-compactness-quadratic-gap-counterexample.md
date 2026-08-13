# Navier–Stokes — compactness does not imply the claimed quadratic active-frame gap

Date: 2026-08-13 UTC

Branch: `automation/b2-round42-repsat-optimal-linear-sketch-20260813`

Exact parent: `stevemoraco/qs@dd9b3afe2984697a2aeecba30147eff5d3c89a79`

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 📚 SOURCE-VERIFIED against arXiv:2605.01873v2; 🟢 PROVED an exact compact algebraic counterexample; 🔴 REFUTED Proposition 2.3 / Lemma 4.4 as proved from compactness and continuity; 🧱 the quantitative active-frame and passive-strain steps require an independent order-two error-bound/transversality theorem; 🔵 LEAN-SOURCE staged separately; ✅ LEAN-VERIFIED pending replay. **NOT A NAVIER–STOKES SOLUTION OR DISPROOF. FIVE-ALARM OFF.**

## 0. Source claim and downstream use

Rishad Shahmurov, *Large-Data Global Regularity for Three-Dimensional Navier--Stokes II: A Direct First-Threshold Continuation Proof for the Full System*, arXiv:2605.01873v2 (5 May 2026), claims a full global continuation theorem.

The paper defines a continuous nonnegative active-frame defect

\[
\mathfrak d(\nu)
=
\mathcal D_{\rm phase}(\nu)
+
\mathcal D_{\rm stall}(\nu)
+
\mathcal D_{\rm netpar}(\nu)
\]

on a compact space of probability measures, with asserted zero set

\[
\mathcal Z=\mathcal Z_{2D}\cup\mathcal Z_{ax}.
\]

Proposition 2.3 and Lemma 4.4 then assert the **quadratic error bound**

\[
\boxed{
\operatorname{dist}(\nu,\mathcal Z)^2
\le C_{\rm fr}\mathfrak d(\nu).
}
\tag{0.1}
\]

The displayed proof uses only finite dimensionality, compactness, continuity, and identification of the zero set. It argues that failure would produce measures at unit distance from `Z` with defect tending to zero.

The same quadratic estimate is load-bearing downstream:

- Lemma 4.5 derives `dist <= C eta^(1/2)` from a defect bound `d<=eta`;
- Lemma 4.6 asserts an aligned passive projection estimate linear in the defect;
- Proposition 2.7 says the squared active-frame distance is therefore controlled by the defect;
- the first-threshold contraction invokes the passive no-dark-matter estimate.

The paper later proves the weaker compact-gap statement

\[
\operatorname{dist}(\nu,\mathcal Z)\ge\epsilon
\Longrightarrow
\mathfrak d(\nu)\ge c(\epsilon)>0,
\tag{0.2}
\]

and mentions a local Łojasiewicz estimate

\[
\operatorname{dist}(\nu,\mathcal Z)^\alpha
\le C\mathfrak d(\nu)
\qquad(\alpha\ge2).
\tag{0.3}
\]

Neither `(0.2)` nor `(0.3)` with an unspecified `alpha>2` implies `(0.1)`.

---

# CLAIMANT

## 1. Exact compact algebraic counterexample

Let

\[
X=[0,1],
\qquad
Z=\{0\},
\qquad
\mathfrak d(x)=x^4.
\]

Then:

1. `X` is compact;
2. `d` is continuous, nonnegative, and polynomial;
3. `d^{-1}(0)=Z`;
4. for every `epsilon>0`, the compact gap `(0.2)` holds with `c(epsilon)=epsilon^4`;
5. the Łojasiewicz-type estimate `(0.3)` holds exactly with exponent `alpha=4` and constant one.

Nevertheless there is no finite `C>=0` such that

\[
x^2\le Cx^4
\qquad\text{for all }x\in[0,1].
\tag{1.1}
\]

### Proof

Fix `C>=0` and choose

\[
x=\frac1{C+1}.
\]

Then `0<x<=1`. Moreover

\[
Cx^2
=
\frac{C}{(C+1)^2}
<1,
\]

because

\[
(C+1)^2-C=C^2+C+1>0.
\]

Multiplying by `x^2>0` gives

\[
Cx^4<x^2.
\]

Thus `(1.1)` fails for every finite `C`. ∎

## 2. Why the source compactness argument proves only a fixed-distance gap

If `(0.1)` fails, one obtains points `nu_n` for which

\[
\frac{\operatorname{dist}(\nu_n,Z)^2}{\mathfrak d(\nu_n)}\to\infty.
\]

Their distances generally tend to zero. One cannot normalize an arbitrary metric-space point to **unit distance** while preserving the defect and remaining inside the same compact label-measure space.

For the counterexample above, take `x_n=1/n`. Then

\[
\operatorname{dist}(x_n,Z)^2=\frac1{n^2},
\qquad
\mathfrak d(x_n)=\frac1{n^4},
\]

so the ratio is `n^2 -> infinity`, but `dist(x_n,Z)->0`, not one.

Compactness does prove `(0.2)`: on the compact set at distance at least `epsilon`, a continuous defect with zero set `Z` has a positive minimum. That statement contains no rate as `epsilon->0`.

## 3. Squared residuals do not repair the exponent automatically

The source emphasizes that the defect is assembled from squared continuous/algebraic residuals. That still does not force order-two growth. A residual can vanish to second order:

\[
F(x)=x^2,
\qquad
|F(x)|^2=x^4.
\]

More geometrically, squared distances to tangentially intersecting constraint sets can have quartic growth relative to distance from their intersection. An order-two error bound requires metric regularity, transversality, a nonsingular Jacobian on every zero stratum, or an equivalent explicit theorem. Compactness is not such a theorem.

---

# CRITIC

## 4. Exact scope

This counterexample does **not** prove that the particular active-frame algebra has quartic degeneracy. It proves that the displayed source proof of `(0.1)` is invalid and that all stated hypotheses used in that proof are insufficient.

The paper could be repaired if its explicit residual map satisfies a uniform order-two error bound. But the manuscript does not provide:

- explicit formulas for the finite residual list sufficient to compute its Jacobian;
- a stratification of the zero set;
- a uniform normal-rank or transversality theorem;
- a proof that every singular stratum still has Łojasiewicz exponent exactly two;
- an independent derivation of the passive projection estimate linear in the defect.

### Critic verdict

🔴 **REFUTED AS PROVED:**

\[
\text{compactness + continuity + exact zero set}
\Longrightarrow
\operatorname{dist}^2\le C\mathfrak d.
\]

The implication is false even for one compact interval and one polynomial defect.

🟠 **CURRENT GLOBAL-REGULARITY CLAIM BLOCKED AS WRITTEN:** Lemmas 4.5 and 4.6 use the missing quadratic rate. A replacement epsilon-splitting argument may be possible, but it must be written with uniform packet normalization and must reproduce the exact linear-defect terms needed in the first-threshold balance. It is not supplied by the compact-gap lemma alone.

## 5. Why the optional Łojasiewicz statement is not enough

For `0<r<1` and `alpha>2`,

\[
r^\alpha<r^2.
\]

Therefore

\[
r^\alpha\le C\mathfrak d
\]

is weaker than the required

\[
r^2\le C'\mathfrak d.
\]

The counterexample `d=r^4` saturates the distinction. To recover Lemma 4.5's square-root closeness and Lemma 4.6's defect-linear projection estimate, the paper needs `alpha=2`, not merely some finite `alpha>=2`.

---

# REBUILDER

## 6. Smallest viable repair

A referee-grade repair can take one of three forms.

### A. Explicit order-two error bound

Write the active-frame residual map

\[
R=(F_1,\ldots,F_M,P)
\]

in finite coordinates and prove a uniform metric-regularity estimate

\[
\operatorname{dist}(\nu,\mathcal Z)
\le C\|R(\nu)\|
\]

on every zero stratum. Squaring gives `(0.1)`.

### B. Weaker-exponent rebudgeting

Accept an exponent `alpha>2`, replace every square-root rigidity rate by `eta^{1/alpha}`, and rederive the passive-strain and first-threshold inequalities with the resulting nonlinear defect powers. No linear absorption may be retained without proof.

### C. Compact-gap epsilon splitting

For each fixed final absorption parameter, split into

\[
\operatorname{dist}<\delta
\quad\text{and}\quad
\operatorname{dist}\ge\delta.
\]

Use small distance to absorb the active projection and the compact minimum `c(delta)` to charge the far case. This requires a uniform a priori bound on the normalized active contribution and a complete recomputation of all constants and descendant thresholds. It proves a different estimate from Lemma 4.6 and must be propagated through the continuation argument.

### 🚧 Exact remaining gap

- explicit active-frame residual coordinates and their zero-set geometry;
- order-two transversality or a complete weaker-exponent rebudgeting;
- a corrected passive-strain visibility theorem;
- the companion Part I theorem, which is independently load-bearing;
- the official Navier–Stokes global regularity theorem.

---

## 7. Lean status

A companion Lean file formalizes:

- compactness of `[0,1]`;
- continuity and zero set of `x^4`;
- for every `C>=0`, an explicit `x in (0,1]` with `Cx^4<x^2`;
- the exact exponent-four salvage.

It does not formalize active-frame measures, Wasserstein/weak metrics, Littlewood--Paley packets, passive strain, or Navier--Stokes.

## 8. Provenance

Primary source checked directly:

- arXiv:2605.01873v2, Proposition 2.3, Lemmas 4.4--4.6, Proposition 2.7, and Theorem 4.7;
- current source date: 5 May 2026.

Exact repository parent: `stevemoraco/qs@dd9b3afe2984697a2aeecba30147eff5d3c89a79`.

**FIVE-ALARM OFF.**
