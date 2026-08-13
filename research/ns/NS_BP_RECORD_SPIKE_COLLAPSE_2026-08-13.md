# Navier–Stokes — Barker–Popkin record spikes must collapse below their natural diffusion time

Date: 2026-08-13 UTC  
Dependencies: Barker–Popkin arXiv:2602.09951v1, Theorem 4.2.2; `NS_BP_ORLICZ_SPIKE_COST_2026-08-13.md`.

**Status:** PROVED conditional consequence for a Leray–Hopf solution smooth before a first singular time; NOT a contradiction; FIVE-ALARM OFF.

## 1. Continuous record charge

Fix a ball `B` around a hypothetical singular point and let

\[
\Phi(s)=\frac{s^3}{L(s)^\theta},\qquad 0<\theta<1.
\]

Choose the fixed high-amplitude cutoff `S_*` from the spike-cost theorem and define

\[
M(t)=\int_B[\Phi(|u(x,t)|)-\Phi(S_*)]_+\,dx.
\tag{1.1}
\]

Before a first singular time `T`, the solution is smooth on every compact subcylinder of `B x (0,T)`. Since the integrand in `(1.1)` is continuous, `M` is continuous on compact time intervals contained in `(0,T)`.

Barker–Popkin imply

\[
\limsup_{t\uparrow T}M(t)=\infty.
\tag{1.2}
\]

Let

\[
E_0=\|u_0\|_2^2.
\]

The spike-cost theorem and Leray–Hopf energy inequality give

\[
\int_{\{M(t)\ge2E_0S_*\}}
M(t)^{4/3}
L\!\left(\frac{M(t)}{2E_0}\right)^{4\theta/3}dt
\le C\frac{E_0^2}{\nu}.
\tag{1.3}
\]

## 2. Disjoint record excursions

Choose `K_0 >= 4E_0S_*` and

\[
K_n=4^nK_0.
\]

By `(1.2)` and continuity, the first hitting time

\[
t_n=\inf\{t<T:M(t)=K_n\}
\]

is well defined after discarding an initial compact time interval if necessary. For `n>=1`, let `s_n` be the last time before `t_n` at which

\[
M(s_n)=K_n/2.
\]

Existence follows because

\[
M(t_{n-1})=K_{n-1}<K_n/2<K_n=M(t_n).
\]

By the last-crossing definition,

\[
M(t)>K_n/2\qquad(s_n<t<t_n).
\tag{2.1}
\]

The intervals

\[
I_n=[s_n,t_n]
\]

are pairwise disjoint. Indeed,

\[
M(t_n)=K_n<K_{n+1}/2=2K_n,
\]

so the next half-level crossing occurs strictly after `t_n`.

## 3. Summable normalized lifetimes

Restrict `(1.3)` to the disjoint intervals `I_n`. From `(2.1)` and monotonicity of `L`,

\[
\sum_{n\ge1}|I_n|
\left(\frac{K_n}{2}\right)^{4/3}
L\!\left(\frac{K_n}{4E_0}\right)^{4\theta/3}
\le C\frac{E_0^2}{\nu}.
\tag{3.1}
\]

Define the natural one-packet diffusion scale associated with charge `K` by

\[
\tau_{\rm nat}(K)
=
\frac{E_0^2}
{\nu K^{4/3}L(K/(4E_0))^{4\theta/3}}.
\tag{3.2}
\]

Then `(3.1)` is exactly

\[
\boxed{
\sum_{n\ge1}
\frac{|I_n|}{\tau_{\rm nat}(K_n)}<\infty.
}
\tag{3.3}
\]

Consequently,

\[
\boxed{
\frac{t_n-s_n}{\tau_{\rm nat}(K_n)}\longrightarrow0.
}
\tag{3.4}
\]

### Theorem NS-BP-RSC1

At a hypothetical first singular time, the Barker–Popkin local Orlicz charge must repeatedly rise from `K_n/2` to `K_n`, for `K_n=4^nK_0`, in a time that is `o(tau_nat(K_n))`. Thus every sufficiently high record excursion is asymptotically faster than the diffusion time of an energy-saturating packet carrying the same charge.

This is stronger than the measure estimate for the full superlevel set: it isolates pairwise disjoint, ordered record excursions and proves summability of their normalized lifetimes.

## 4. Exact remaining rigidity theorem

The next gate is now one-sided and scaling matched.

### `NS-BP-NO-SUBDIFFUSIVE-RISE`

Prove that a suitable Navier–Stokes solution cannot increase the local Barker–Popkin charge from `K/2` to `K` in `o(tau_nat(K))` near a first singular point, unless the excursion creates a quantitatively comparable fresh pressure-flux, vorticity, or localized-forcing charge; prove that those alternative charges are disjoint or Carleson-summable across record levels.

Any uniform lower bound

\[
t_n-s_n\ge c\,\tau_{\rm nat}(K_n)
\]

for infinitely many record levels contradicts `(3.3)` immediately.

Barker–Popkin's critically bounded forced estimates are designed to control the forcing introduced by localization, while Barker's quantitative physical-space work supplies propagation/no-return information for vorticity concentration. Those are the natural primary tools for this gate.

## 5. Hostile scope audit

- Continuity is used only before the first singular time, where the solution is smooth.
- Unbounded limsup is not upgraded to monotone divergence; first-hit and last-half-hit times handle oscillation explicitly.
- Disjointness follows from the geometric factor `4`; it is not assumed.
- `(3.4)` is a necessary singularity scenario, not a contradiction.
- A functional time-localized countermodel can realize arbitrarily narrow spikes, so the missing lower bound must use the Navier–Stokes equation.
- No Clay theorem is claimed.

\[
\boxed{\text{FIVE-ALARM OFF.}}
\]
