# Navier–Stokes — fast activation makes the exact conjugate sideband nonperturbative

Date: 2026-08-13 UTC

Status legend: 🟢 PROVED, 🔵 LEAN-SOURCE, ✅ LEAN-VERIFIED, 🟡 CONDITIONAL, 🟠 SUSPECT, 🔴 REFUTED, 🧱 OBSTRUCTION, 📚 SOURCE-VERIFIED, 🧩 BRIDGE, 🚧 MISSING.

**Status:** 🟢 PROVED exact scalar heat-response theorem and exponent consequence; 🔴 REFUTED the current use of a short causal Duhamel interval to make the banked order-one conjugate sideband power-small; 🧱 the pressure-canceling isolated real triad still requires exact sideband cancellation or promotion of the sideband into the principal state; 🔵 LEAN-SOURCE finite scalar core staged separately; ✅ LEAN-VERIFIED pending replay. **NOT A NAVIER–STOKES PROOF OR DISPROOF. FIVE-ALARM OFF.**

## 1. The two banked facts that must be combined

### Exact sideband fact

For the real pressure-canceling equal-shell triad, the intended low-to-high feed and the unwanted conjugate sideband have exactly equal Leray-visible coefficient magnitude. In the banked notation,

`|S|/I=1`.

Thus, on the shell activation interval, the unwanted sideband forcing is not an envelope-small remainder. It is the same scale as the intended forcing that changes the principal high-shell amplitude.

### Fast activation fact

Palasek's viscous parameter window uses

`K=N^b`,

`Delta t ~ N^(-beta)`,

with

`beta>2b`.

Therefore

`z:=K^2 Delta t ~ N^(2b-beta) -> 0`.

The activation interval is much shorter than the heat time `K^-2`.

These two facts were previously audited separately. Their combination is load-bearing.

## 2. Exact scalar heat response

Consider one Fourier sideband mode with carrier magnitude `K` and constant forcing `E` on an interval of length `tau`, with zero incoming corrector data:

`w'(t)+K^2 w(t)=-E`,

`w(0)=0`.

The exact solution at the end of the interval is

`w(tau)=-(1-exp(-K^2 tau)) E/K^2.`

Suppose the intended principal shell amplitude changes by `X` over the same interval and the sideband forcing equals the intended feed scale:

`E=X/tau`.

Then

`boxed:
|w(tau)|/|X|
 = (1-exp(-z))/z,
 z=K^2 tau.`

As `z->0`,

`boxed: (1-exp(-z))/z -> 1.`

More quantitatively, for `0<z<=1`, the elementary inequality

`exp(-z) <= 1-z+z^2/2`

gives

`(1-exp(-z))/z >= 1-z/2 >= 1/2.`

Hence every sufficiently high shell obeys

`boxed: |w(tau)| >= |X|/2.`

The correction is not `o(X)`. It carries a fixed fraction of the principal shell amplitude.

## 3. Why the causal upper bound does not imply smallness

The banked Duhamel estimate is

`||w|| <= min(tau,K^-2) ||E||.`

In the fast-activation regime `tau<<K^-2`, this becomes

`||w|| <= tau ||E||.`

For an envelope-small residual this can be useful. But for the exact conjugate sideband,

`||E_side|| ~ ||X||/tau`,

so the bound only gives

`||w_side|| <= O(X)`.

It does not give a negative power of `N`. The exact scalar formula above shows that the order-one upper bound is sharp: the ratio tends to one.

The logical error is therefore not in the causal Duhamel estimate. It is in applying an envelope-defect amplitude to a different channel whose coefficient was already proved equal to the intended feed.

## 4. Exponent statement

With

`tau=N^(-beta)`,

`K=N^b`,

`beta>2b`,

we have

`z=N^(2b-beta)->0`.

Thus the high-shell limit is

`|w_side|/|X| -> 1`.

No admissible choice inside the Palasek viscous window changes this conclusion. Indeed, the strict inequality `beta>2b` is exactly what makes the nonlinear activation faster than viscous damping; it simultaneously prevents heat damping from suppressing an equal-strength sideband during the activation.

## 5. Claim + counterexample + salvage

### Claim killed

Because `Delta t << K^-2`, the causal Duhamel corrector gains the short factor `Delta t` and makes every high-frequency sideband power-small relative to the principal shell.

### Counterexample

Take the already-banked real conjugate sideband whose forcing coefficient equals the intended feed. If the intended shell changes by `X` over `Delta t`, then `E_side=X/Delta t`. The exact heat response satisfies

`|w_side|/|X|=(1-exp(-K^2 Delta t))/(K^2 Delta t)->1`.

### Best salvage

One of the following is now mandatory:

1. add modes that cancel each conjugate sideband exactly at the Fourier level;
2. enlarge the principal packet/state so the sideband is a tracked shell variable rather than an error;
3. prove a nonlinear normal form that cancels the equal-strength sideband without introducing an order-one velocity correction;
4. find a different real polarization geometry in which the low-to-high sidebands are pure gradients while the intended feed survives.

A generic causal Stokes/Duhamel correction is not a salvage for this channel.

## 6. Assumptions and critic verdict

### Assumptions

- The exact coefficient equality `|S|=I` from the banked real-triad calculation.
- A principal amplitude change of order `X` over activation time `tau`.
- The sideband is spectrally localized at carrier magnitude comparable to `K`.
- The scalar heat equation gives the most favorable uncoupled damping model; transport or nonlinear coupling is not used to improve the lower bound.

### Critic verdict

🟢 **SURVIVES.** The response formula is exact, and the conclusion uses the same fast-activation inequality required by the shell blow-up window.

🔴 **REFUTED:** short-time causality alone makes an equal-strength sideband perturbative.

🟡 **CONDITIONAL:** a larger exact cancellation circuit may still repair the embedding.

## 7. Lean status

- 🔵 LEAN-SOURCE: `verification/b2-round42/NSFastActivationSidebandFirewall.lean` formalizes the finite scalar implication that an attenuation factor at least `1/2` and a sideband feed `E tau=X` force a correction at least `X/2`, together with the exponent-sign arithmetic at `(b,beta)=(17/16,35/16)`.
- ✅ LEAN-VERIFIED: pending clean replay.
- The exponential solution formula, Fourier triad coefficient equality, heat semigroup, Navier–Stokes equation, and Palasek shell theorem are not formalized.

## 8. Exact remaining gap

🚧 MISSING — an exact real Fourier cancellation/closure theorem for all low-to-high conjugate sidebands, followed by a full nonlinear shadowing theorem in the physical periodic Navier–Stokes equations.

## 9. Provenance

- Exact round parent: `stevemoraco/qs@e345ef906a7b809e3c47e949e556b6417247ed06`.
- Banked equal-sideband theorem: `stevemoraco/RH@d38ad91c04ee063a14b499cd2c82ebb841d539bf`.
- Banked causal-Duhamel note: `stevemoraco/RH@c4d0c8aa27599bb7d573c1b832f87ddb97e44df7`.
- Banked high-frequency energy gate: `stevemoraco/RH@95b7bf8a09586b0ae402268c4c0be5e39ac31424`.
- Explicit parameter point: `stevemoraco/RH@244fab9862a836846d1adde9580234365736e2a2`.
- Palasek source: Stan Palasek, *Finite-time blow-up in an elementary model of the 3D Navier–Stokes equations*, arXiv:2605.13827.

**FIVE-ALARM OFF.**
