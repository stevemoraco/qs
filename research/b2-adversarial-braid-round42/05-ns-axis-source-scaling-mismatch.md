# Navier–Stokes — the companion axisymmetric theorem rescales its source with the wrong homogeneity

Date: 2026-08-13 UTC

Branch: `automation/b2-round42-repsat-optimal-linear-sketch-20260813`

Exact parent: `stevemoraco/qs@6c2d06104d2c558643d6a1428dcc2a324f0301bb`

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 📚 SOURCE-VERIFIED against arXiv:2605.01875v2; 🟢 PROVED exact lifted-equation and measure-scaling identities; 🔴 REFUTED the manuscript's claimed parabolic invariance of its source rescaling and source norm; 🧱 Theorem 3.1, the local continuation gate used by the whole axisymmetric proof, is not obtained from the displayed unit-scale argument. 🔵 LEAN-SOURCE staged separately; ✅ LEAN-VERIFIED pending replay. **NOT A NAVIER--STOKES SOLUTION OR DISPROOF. FIVE-ALARM OFF.**

## 0. Source statements

Rishad Shahmurov, *Large-Data Global Regularity for Three-Dimensional Navier--Stokes I: A Direct First-Threshold Continuation Proof for the Axisymmetric Swirl Class*, arXiv:2605.01875v2 (5 May 2026), is the companion endpoint theorem used by Part II.

The manuscript defines

\[
\Gamma=ru_\theta,
\qquad
G=\omega_\theta/r,
\qquad
d\mu_5=r^3drdz,
\]

and chooses a source variable `Gamma_e` satisfying

\[
r^{-4}\partial_z(\Gamma^2)
=
\partial_z(\Gamma_e^2).
\tag{0.1}
\]

Since `r` is independent of `z`, the natural physical choice is

\[
\Gamma_e=\Gamma/r^2=u_\theta/r,
\tag{0.2}
\]

up to a sign and any separately justified `z`-independent square correction.

The lifted equation is stated as

\[
\partial_tG+u\cdot\nabla_5G
=
\Delta_5G-\partial_z(\Gamma_e^2).
\tag{0.3}
\]

Theorem 3.1 defines

\[
\mathcal A_R
=
R^{-2}\iint_{Q_R^-}|\Gamma_e|^4d\mu_5dt
\tag{0.4}
\]

and claims that reduction to the unit cylinder follows from

\[
\widetilde G(y,s)
=R^3G(z_0+Ry,t_0+R^2s),
\qquad
\widetilde\Gamma_e(y,s)
=R^{3/2}\Gamma_e(z_0+Ry,t_0+R^2s),
\tag{0.5}
\]

with powers “exactly” making the score and `(0.4)` invariant.

---

# CLAIMANT

## 1. Equation invariance determines the source exponent uniquely

Consider the model source-diffusion equation

\[
\partial_tG
=
\Delta_5G-\partial_z(H^2).
\]

Under

\[
\widetilde G(y,s)=R^aG(Ry,R^2s),
\qquad
\widetilde H(y,s)=R^bH(Ry,R^2s),
\]

the time derivative and diffusion terms both acquire exponent

\[
R^{a+2}.
\]

The source becomes

\[
\partial_{y_z}(\widetilde H^2)
=
R^{2b+1}\partial_z(H^2).
\]

Therefore equation invariance requires

\[
\boxed{a+2=2b+1.}
\tag{1.1}
\]

For the manuscript's correct lifted-vorticity exponent `a=3`, condition `(1.1)` gives uniquely

\[
\boxed{b=2.}
\tag{1.2}
\]

This agrees with the physical identity `(0.2)`: under Navier--Stokes scaling, `u_theta` has exponent one and division by `r` adds one more power.

The paper instead takes

\[
b=3/2.
\]

Then

\[
a+2=5,
\qquad
2b+1=4.
\]

The normalized source is one full power short. Substitution of `(0.5)` into `(0.3)` does **not** reproduce the same unit-scale equation.

## 2. The displayed source norm is not invariant under the paper's own rescaling

The lifted spatial measure has five-dimensional homogeneity:

\[
d\mu_5(Ry)=R^5d\mu_5(y).
\]

Including `dt=R^2ds`, spacetime measure has homogeneity `R^7`.

Under the paper's exponent `b=3/2`,

\[
\begin{aligned}
\iint_{Q_1}|\widetilde\Gamma_e|^4d\mu_5(y)ds
&=
R^{4b-7}
\iint_{Q_R}|\Gamma_e|^4d\mu_5(x)dt\\
&=
R^{-1}
\iint_{Q_R}|\Gamma_e|^4d\mu_5dt.
\end{aligned}
\tag{2.1}
\]

Thus even if `b=3/2` were accepted, the quantity matching the unit integral would be

\[
R^{-1}\iint|\Gamma_e|^4,
\]

not the manuscript's

\[
R^{-2}\iint|\Gamma_e|^4.
\]

The claim of invariance in Theorem 3.1 is arithmetically false.

## 3. The physically correct source norm

With the equation-preserving exponent `b=2`,

\[
4b-7=1.
\]

Hence

\[
\iint_{Q_1}|\widetilde\Gamma_e|^4
=
R\iint_{Q_R}|\Gamma_e|^4.
\]

The scale-invariant physical source quantity is therefore

\[
\boxed{
R\iint_{Q_R}|\Gamma_e|^4d\mu_5dt,
}
\tag{3.1}
\]

not `(0.4)`.

Equivalently, under the forward Navier--Stokes scaling by `lambda`,

\[
\mathcal A^-_{R/\lambda}[\Gamma_{e,\lambda}]
=
\lambda^3\mathcal A^-_R[\Gamma_e]
\]

for the manuscript's `R^{-2}` normalization. It is supercritical by three powers.

---

# CRITIC

## 4. Could `Gamma_e` be assigned an artificial exponent?

Not while retaining the displayed physical source equation. The identity `(0.1)` types `Gamma_e^2` as `Gamma^2/r^4`; its physical exponent is four, so `Gamma_e` has exponent two. More generally, equation invariance itself forces `(1.2)`.

One could introduce a different normalized auxiliary variable with exponent `3/2`, but then the equation acquires an explicit scale coefficient. The paper does not include such a coefficient.

### Critic verdict

🔴 **REFUTED:** the rescaling `(0.5)` preserves the lifted equation and makes `(0.4)` invariant.

🧱 **COMPANION THEOREM BLOCKED AS WRITTEN:** Theorem 3.1 says the general-radius local regularity criterion follows from the unit theorem by the displayed scaling. It does not. Every subsequent first-threshold, source-selection, descendant, and continuation argument imports Theorem 3.1.

## 5. Independent dimensional symptom in the conclusion

Theorem 3.1 gives the common bound

\[
\|G\|_\infty+\|\Gamma_e\|_\infty+R\|\nabla\Gamma_e\|_\infty
\le C R^{-3}.
\]

The `R^{-3}` exponent is natural for `G`, but the physical source `Gamma_e=u_theta/r` scales as `R^{-2}`. Assigning both fields the same endpoint exponent is another manifestation of the type collapse.

This observation is diagnostic; the decisive failures are the exact equation and source-integral calculations above.

---

# REBUILDER

## 6. Minimum repair

A valid repair must:

1. use
   \[
   \widetilde\Gamma_e=R^2\Gamma_e;
   \]
2. replace `A_R` by the invariant quantity `(3.1)`;
3. reprove the De Giorgi iteration with that source norm;
4. state separate endpoint powers `R^{-3}` for `G` and `R^{-2}` for `Gamma_e`;
5. rederive every source-to-score selection and descendant estimate;
6. recompute the first-threshold balance;
7. then re-audit the Ekeland--Pohozaev strict bridge independently.

Changing `R^{-2}` to `R` is not cosmetic: it changes the small-scale strength by three powers.

### 🚧 Exact remaining gap

- corrected local regularity theorem at arbitrary radius;
- corrected source selection and finite-overlap extraction;
- strict full-Dirichlet bridge in the corrected class;
- global axisymmetric continuation;
- Part II's independently broken full-dimensional front end;
- the official Navier--Stokes theorem.

---

## 7. Lean status

A companion finite Lean file formalizes:

- the exponent equation `a+2=2b+1` and its unique solution `b=2` at `a=3`;
- failure of the paper's `b=3/2` exponent;
- spacetime integral exponent `4b-7`;
- values `-1` at `b=3/2` and `1` at `b=2`;
- the three-power mismatch between `R^{-2}` and the physical invariant `R`.

It does not formalize cylindrical coordinates, the lifted PDE, measures, De Giorgi iteration, or Navier--Stokes.

## 8. Provenance

Primary source checked directly:

- arXiv:2605.01875v2, equations (1)--(2), Definition 1.1, and Theorem 3.1;
- current source date: 5 May 2026.

Exact repository parent: `stevemoraco/qs@6c2d06104d2c558643d6a1428dcc2a324f0301bb`.

**FIVE-ALARM OFF.**
