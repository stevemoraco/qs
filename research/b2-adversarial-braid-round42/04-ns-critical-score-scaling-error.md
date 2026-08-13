# Navier–Stokes — the claimed critical packet score has the wrong scaling exponent

Date: 2026-08-13 UTC

Branch: `automation/b2-round42-repsat-optimal-linear-sketch-20260813`

Exact parent: `stevemoraco/qs@8f9cca2a4f3c387e9d4a69411f5cc7fe806dcf4b`

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 📚 SOURCE-VERIFIED against arXiv:2605.01873v2; 🟢 PROVED exact Navier--Stokes scaling calculation; 🔴 REFUTED the manuscript's statement that its Definition 1.2 score is scale invariant; 🧱 every unit-packet normalization and critical-threshold statement using that invariance must be rederived. 🔵 LEAN-SOURCE staged separately; ✅ LEAN-VERIFIED pending replay. **NOT A NAVIER--STOKES SOLUTION OR DISPROOF. FIVE-ALARM OFF.**

## 0. Source definition

Definition 1.2 of Rishad Shahmurov, *Large-Data Global Regularity for Three-Dimensional Navier--Stokes II: A Direct First-Threshold Continuation Proof for the Full System*, arXiv:2605.01873v2, states that the exponent `alpha_*=1` gives a scale-invariant local vorticity score and defines

\[
\mathcal Q^{3D}(Q)
=
\rho_Q^{-1}
\sup_{t\in(t_Q-\rho_Q^2,t_Q]}
\int_{B_{\rho_Q}(x_Q)}|\omega(x,t)|^2\,dx.
\tag{0.1}
\]

The fixed-time version is

\[
\mathcal Q^{3D}_\rho(x_0,t)
=
\rho^{-1}
\int_{B_\rho(x_0)}|\omega(x,t)|^2\,dx.
\tag{0.2}
\]

The paper later rescales selected packets to unit size and says the local bounds and score normalization are invariant up to universal constants.

---

# CLAIMANT

## 1. Exact Navier--Stokes scaling

For `lambda>0`, the three-dimensional Navier--Stokes scaling is

\[
u_\lambda(x,t)=\lambda u(\lambda x,\lambda^2t).
\]

Therefore

\[
\omega_\lambda(x,t)
=
\lambda^2\omega(\lambda x,\lambda^2t).
\]

Let

\[
I(\rho,t)
=
\int_{B_\rho}|\omega(x,t)|^2\,dx.
\]

At the corresponding scaled radius `rho/lambda` and time `t/lambda^2`, change variables `y=lambda x`:

\[
\begin{aligned}
I_\lambda(\rho/\lambda,t/\lambda^2)
&=
\int_{B_{\rho/\lambda}}
\lambda^4|\omega(\lambda x,t)|^2\,dx\\
&=
\lambda
\int_{B_\rho}|\omega(y,t)|^2\,dy\\
&=
\lambda I(\rho,t).
\end{aligned}
\tag{1.1}
\]

The same factor holds after taking the supremum over the corresponding parabolic time interval.

## 2. The manuscript score is supercritical by two powers

Substitute `(1.1)` into `(0.2)`:

\[
\begin{aligned}
\mathcal Q^-_{\rho/\lambda}[u_\lambda]
&=
(\rho/\lambda)^{-1}\,\lambda I(\rho)\\
&=
\lambda^2\rho^{-1}I(\rho)\\
&=
\boxed{\lambda^2\mathcal Q^-_\rho[u]}.
\end{aligned}
\tag{2.1}
\]

Thus the displayed score is **not invariant**. It has scaling homogeneity `+2`.

The scale-invariant fixed-time spatial vorticity score is instead

\[
\boxed{
\mathcal Q^+_\rho[u]
=
\rho\int_{B_\rho}|\omega|^2dx.
}
\tag{2.2}
\]

Indeed,

\[
(\rho/\lambda)\cdot\lambda I(\rho)
=
\rho I(\rho).
\]

The factor `rho^{-1}` is appropriate for the **spacetime** dissipation integral

\[
\rho^{-1}
\iint_{Q_\rho}|\omega|^2\,dxdt,
\]

because `dxdt` contributes `lambda^{-5}`, making the spacetime integral scale as `lambda^{-1}`. The manuscript uses a time supremum of spatial integrals, not a spacetime integral.

---

# CRITIC

## 3. Exact scope

A supercritical envelope can still be mathematically meaningful. The countercalculation does not prove that no theorem can be built from `(0.1)`. It proves that every argument treating `(0.1)` as critical or invariant is invalid without a new scale-dependent ledger.

The mismatch is load-bearing because the manuscript repeatedly performs the following arrows:

\[
\text{selected packet at radius }\rho
\longrightarrow
\text{unit packet}
\longrightarrow
\text{same threshold/score normalization}.
\]

Under `(2.1)`, the score changes by `rho^{-2}` when a radius-`rho` packet is rescaled to unit size. This is not a universal constant as `rho->0`.

### Critic verdict

🔴 **REFUTED:** Definition 1.2 is a scale-invariant local vorticity score.

🧱 **PROOF ARCHITECTURE BLOCKED AS WRITTEN:** The first-threshold selection, descendant score persistence, unit-size normalization, and continuation envelope must all be audited with the correct homogeneity. A phrase such as “invariant up to universal constants” cannot absorb a factor depending quadratically on the packet scale.

## 4. Smallest counterexample to invariance

Take any smooth solution/time slice with

\[
I(\rho)>0
\]

and choose `lambda=2`. Then

\[
\mathcal Q^-_{\rho/2}[u_2]
=4\mathcal Q^-_\rho[u],
\]

not the same score. No subtle limit, boundary convention, or angular decomposition is involved.

---

# REBUILDER

## 5. Possible repairs

### A. Correct the spatial score

Replace `(0.1)` by

\[
\rho_Q
\sup_t\int_{B_{\rho_Q}}|\omega|^2dx
\]

and reprove every threshold, descendant, visibility, and contraction estimate. This changes the relative powers of all error channels.

### B. Use the spacetime critical score

Replace the time supremum by

\[
\rho_Q^{-1}
\iint_{Q_Q}|\omega|^2dxdt.
\]

Again the entire proof must be retyped because a spacetime integral does not provide the same endpoint-time packet score.

### C. Keep the supercritical score honestly

Retain `(0.1)` but track the exact `lambda^2` factor under every rescaling. Then prove a scale-dependent first-threshold theorem strong enough to survive `rho->0`. The current scale-free constants and unit-packet reductions do not supply this.

### 🚧 Exact remaining gap

- choose a correctly typed critical or supercritical envelope;
- rederive local continuation from that envelope;
- prove score persistence under every descendant map with the correct scale ratios;
- recompute all visibility and defect normalizations;
- repair the independent compactness-to-quadratic-gap error;
- verify the companion Part I theorem;
- prove the official global regularity alternative.

---

## 6. Lean status

A companion finite Lean file formalizes only the scalar homogeneity identities:

\[
\operatorname{badScore}(\rho/\lambda,\lambda I)
=
\lambda^2\operatorname{badScore}(\rho,I),
\]

and

\[
\operatorname{goodScore}(\rho/\lambda,\lambda I)
=
\operatorname{goodScore}(\rho,I).
\]

It does not formalize Navier--Stokes scaling, vorticity, integrals, balls, or the manuscript.

## 7. Provenance

Primary source checked directly:

- arXiv:2605.01873v2, Definition 1.2, Theorems 5.1--5.2, and descendant-normalization passages;
- current source date: 5 May 2026.

Exact repository parent: `stevemoraco/qs@8f9cca2a4f3c387e9d4a69411f5cc7fe806dcf4b`.

**FIVE-ALARM OFF.**
