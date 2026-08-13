# B2 adversarial firewall — PNP + Navier–Stokes — 2026-08-13

Status: research only. FIVE-ALARM OFF.

## P vs NP: upstream restriction-averaging theorem is false as stated

**🔴 REFUTED · 🧱 OBSTRUCTION · 🔵 LEAN-SOURCE · 🚧 MISSING replay**

### Exact claim attacked

In `Stevemoraco/RH-Lean` commit `ba99f4cbdd8842ae63817890c8538685130bc2ab`, theorem `local_to_global_error_floor` assumes `μ >= 0` and `err >= 0`, but does not assume `ν >= 0`. Its proof nevertheless needs every bad-restriction local error to be nonnegative.

### Counterexample

Take `R={g,b}`, `X={x}`, with only `g` good. Set

- `μ(g)=μ(b)=1/2`;
- `ν(g,x)=1`, `ν(b,x)=-3`;
- `err(x)=1`;
- `ρ=1/2`, `η=1`.

Then all stated upstream hypotheses hold: outer weights and error are nonnegative, good mass is `1/2`, and the good local error is `1 >= η`. But the conclusion becomes

`1/2 <= (1/2)*1 + (1/2)*(-3) = -1`,

which is false.

**🟢 PROVED:** a nonnegativity hypothesis on `ν` is necessary for that theorem statement/proof strategy.

### Correction already present downstream

`Stevemoraco/qs` commit `6b5f836968a60bbbbe1d2fd9a524e38cc476144f` adds `hν : ∀ r x, 0 ≤ ν r x` (and `0 ≤ η`). This blocks the counterexample.

### Replay audit

The first `qs` replay, run `31704038848`, never reached Lean. `lake update` failed because the project pinned nonexistent Mathlib revision `9c9a8e0a102b73c62db72c0e12a38522b2a1bd1c`. Mathlib tag `v4.19.0` resolves to real commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

This isolated branch repairs the pin in commit `26675caf59e0cb5952feccd7b35d9ec0f2fb9c21` and enables branch replay in commit `9eb0b672a4a1279b31c2d8295d0c19b382c31dee`.

### Critic verdict

Even a green replay proves only finite averaging after a local error floor is supplied. It does not define Boolean circuits, P, NP, or `P != NP`.

### Lean status

Upstream theorem: **🔴 REFUTED as stated**. Corrected downstream file: **🔵 LEAN-SOURCE**. Kernel replay: **🚧 MISSING until CI finishes green**.

### Exact remaining gap

**🚧 MISSING:** a circuit-independent local restriction hardness theorem in the exact size/depth regime, plus a complexity-preserving bridge from that theorem to a superpolynomial lower bound for an NP language.

### Provenance

`RH-Lean` `ba99f4c...`; `qs` `6b5f836...`, `37edf13...`; failed Actions run `31704038848`; Mathlib `v4.19.0 -> c44e0c8...`.

---

## Navier–Stokes: newest sqrt(2) relay has a pump-sign mismatch

**🔴 REFUTED displayed instability claim · 🧱 OBSTRUCTION · 🟠 SUSPECT handoff · 🚧 MISSING PDE bridge**

### Exact claim attacked

`Stevemoraco/RH` commit `02f6cad47353726ed61b87e5da64ff66f5406f1e` displays

`x'=-a y z`, `y'=b x z`, `z'=c x y`,

with `a,b,c>0`, then says that with `q` as the pump the linearized seed pair is unstable.

### Exact linearization

Freeze the displayed `y` pump at `Y != 0`. Then

`x'=-aYz`, `z'=cYx`,

so

`x''=-ac Y^2 x`.

The characteristic equation is `r^2 + acY^2 = 0`, hence the eigenvalues are purely imaginary. The displayed system is oscillatory around the `y` pump, not exponentially unstable.

Freeze `x=X` instead:

`y'=bXz`, `z'=cXy`, hence `y''=bcX^2 y`, which is hyperbolic. The printed signs support an unstable `x` pump, not the asserted `q`/`y` pump.

**🟢 PROVED:** the instability sentence is internally inconsistent with the printed ODE; no external helical convention is needed.

### Critic verdict

The integer carrier ladder may survive, but the dynamical handoff is not proved. The favorable high-child fraction is naturally derived in the unstable `x`-pump orientation, while the relay text promotes the high child to the next `q` pump. A permutation/helicity sign theorem is required before localization.

### Lean status

No Lean theorem in the cited commit verifies this instability/handoff. **🚧 MISSING.**

### Exact remaining gap

**🧩 BRIDGE / 🚧 MISSING:** prove a consistent variable/helicity/orientation permutation for every generation such that the inherited high child is the unstable next pump and the favorable energy fraction survives; then prove the full real-valued conjugate/exterior localized packet stability with viscosity uniformly across generations.

### Provenance

`Stevemoraco/RH` commit `02f6cad47353726ed61b87e5da64ff66f5406f1e`, 2026-08-13.
