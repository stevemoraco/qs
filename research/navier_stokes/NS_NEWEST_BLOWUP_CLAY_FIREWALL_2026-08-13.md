# Newest Navier--Stokes blow-up results versus the Clay alternatives

**Date:** 2026-08-13  
**Status:** theorem/quantifier audit and time-reversal obstruction; **not a
Navier--Stokes regularity or breakdown theorem**.

## 1. Exact official target

Fefferman's official periodic breakdown alternative (D) asks for a smooth
periodic divergence-free initial field and a smooth periodic force, rapidly
decaying with every time derivative, for which **no**
`C∞(R³ × [0,∞))` periodic solution exists.

Source: Charles Fefferman,
[Existence and Smoothness of the Navier--Stokes Equation](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf),
conditions (8)--(11) and alternative (D).

The quantifier `no smooth solution exists` is essential.  Existence of a bad
weak solution, even one that is spatially smooth at every individual time,
does not imply (D).

## 2. Cheskidov--Dai--Palasek (2026)

Theorem 1.1 of Cheskidov--Dai--Palasek constructs, for every smooth
divergence-free periodic datum, a weak solution which

- agrees with the ordinary classical solution through a chosen time `T*`;
- is classical separately on `[0,T*]` and `(T*,T]`;
- blows up in `L∞` as `t → T*+`;
- is weak-* continuous in `BMO⁻¹`.

The paper simultaneously identifies the ordinary classical branch from the
same smooth trace at `T*`.  Remark 1.4 states that the anomalous branch is in
neither `L∞_t L²_x` nor `L²_t H¹_x` near `T*`; Theorem 2.4 proves that its
energy diverges from the right.  Thus it is not a Leray--Hopf branch and is not
spacetime-smooth across `T*`.

Source: Alexey Cheskidov, Mimi Dai, Stan Palasek,
[Instantaneous Type I blow-up and non-uniqueness of smooth solutions of the
Navier--Stokes equations](https://arxiv.org/abs/2511.09556), arXiv
2511.09556v2, Theorems 1.1, 1.7, 2.4 and Remark 1.4.

**Claimant.** This is a rigorous complete inverse cascade and an anomalous
weak branch from smooth data.

**Critic.** It proves coexistence of a bad weak branch and a good classical
branch.  Clay (D) requires nonexistence of every global smooth branch.  The
paper itself distinguishes its right-hand instantaneous blow-up from the
still-open left-hand terminal blow-up of the unique classical solution.

**Rebuilder.** The construction is valuable input for an inverse-cascade
gadget, but a Clay route must turn it into a forward terminal singularity
without importing singular forcing or abandoning the classical solution
class.

## 3. Galdi--Gazzola (2026)

Galdi--Gazzola construct unique global Leray--Hopf solutions with several
norms blowing up at countably many instants.  Their main force classes include
`L²_loc,t L^(6/5)_x` and `L^(5/4)_loc,t L²_x`; later results approach other
regularity thresholds.  These are not the `C∞`, rapidly time-decaying forces
required by Fefferman (C)/(D), and the constructed solution remains a global
Leray--Hopf solution.

Source: Giovanni Paolo Galdi, Filippo Gazzola,
[Blow-up and uniqueness of Leray-Hopf solutions to forced Navier--Stokes
equations](https://arxiv.org/abs/2606.15189), arXiv 2606.15189v3.

**Best salvage:** their explicit Lane--Emden cancellation is a candidate
stress/forcing gadget.  The first missing bridge is an upgrade from
supercritical force regularity to Fefferman's smooth force while retaining
breakdown of all classical solutions.

## 4. Exact time-reversal firewall

Write the Leray-projected unforced equation schematically as

[
  partial_s u = 
uDelta u - N(u),qquad N(-u)=N(u).
]

For the sign-reversed reflection `v(t)=-u(T-t)`,

[
  partial_t v=partial_s u,qquad
  Delta v=-Delta u,qquad N(v)=N(u).
]

Consequently,

[
  partial_t v-
uDelta v+N(v)=2
uDelta u.
]

The companion Lean file proves this identity componentwise and proves the
residual is nonzero when (
u
e0) and the relevant Laplacian component is
nonzero.

This is not merely a sign inconvenience.  On the torus, if the proposed
forcing `2νΔu` extended smoothly through the reflected terminal time, then
elliptic inversion would keep the mean-zero part of `u` smooth and bounded;
the mean is conserved.  That contradicts the inverse-cascade branch's
`L∞` blow-up.  Therefore direct time reversal cannot convert the 2026
instantaneous branch into Fefferman (D).

## 5. Correct next gate

A viable conversion must supply an additional nonlinear pump whose exact
all-scale interaction cancels `2νΔu`, with the **remaining external
residual extending C∞ and rapidly decaying through the terminal time**.  Every
frequency scale, cross-scale return, localization error, and infinite-limit
interchange is part of that theorem.

No such bridge is proved here.

**SIX-ALARM: OFF.**
