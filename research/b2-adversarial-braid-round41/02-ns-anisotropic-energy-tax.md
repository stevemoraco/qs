# Navier--Stokes: normal synchronization does not supply total-energy contraction

Date: 2026-08-13

## Status

🟢 PROVED finite two-replica amplitude theorem.

🧱 OBSTRUCTION to upgrading replica-defect contraction into contraction of the
full packet energy.

No Navier--Stokes solution or blow-up theorem is claimed.

## Exact setup

For real amplitudes `a,b`, common tangent gain `g`, and synchronization coupling
`kappa`, set

`m=(a+b)/2`, `d=a-b`,

and

`a' = g a - kappa(a-b)`,

`b' = g b + kappa(a-b)`.

The banked survivor already proves

`m' = g m`,

`d' = (g-2 kappa)d`,

so a relative normal contraction `|d'| <= q g |d|`, `q<1`, requires
`kappa >= (1-q)g/2`.

## New theorem: exact energy decomposition

The Euclidean two-replica energy has the identity

`(a')^2+(b')^2
 = 2 g^2 m^2 + ((g-2 kappa)^2/2)d^2`.

Equivalently, synchronization can change only the normal-energy multiplier.
The tangent diagonal retains multiplier `g^2` exactly.

On the diagonal `a=b!=0`, one has `d=0` and therefore

`(a')^2+(b')^2 = g^2(a^2+b^2)`.

Consequently, if `g>1`, then for every `kappa`

`(a')^2+(b')^2 > a^2+b^2`.

This remains true at the midpoint coupling `kappa=g/2`, which kills the normal
defect in one step.  Exact normal synchronization therefore does not make the
full map dissipative.

## Proof

Use the elementary identity

`a^2+b^2 = 2((a+b)/2)^2 + (a-b)^2/2`

both before and after the synchronized step, together with the exact mean and
defect multipliers.  The diagonal conclusion follows by setting `a=b`; strict
expansion follows from `(g^2-1)a^2>0` when `g>1` and `a!=0`.

## Claim + counterexample + salvage

### Claimant

A replicated-amplifier packet manifold might gain a normal spectral gap by
adding synchronization while retaining tangent cascade amplification.

### Critic

That statement is genuinely anisotropic.  Even perfect one-step removal of the
replica defect leaves the tangent diagonal amplified by `g`; no estimate in the
ordinary total two-replica energy can be contractive when `g>1`.

Thus “normal hyperbolicity” cannot silently be replaced by a global `L^2`
contraction or by a total-energy Lyapunov estimate.

### Rebuilder

The route is not dead.  Normal hyperbolicity is supposed to be anisotropic.
The required object is now typed precisely:

🧩 BRIDGE — construct an invariant or approximately invariant divergence-free
packet manifold with an anisotropic Lyapunov norm that contracts transverse
errors while allowing tangent transfer, and simultaneously prove that the
actual Navier--Stokes energy identity, viscosity, pressure/Leray projection,
and off-manifold leakage close at every recursive scale.

Any tangent growth must be paid for by redistribution and viscous dissipation
elsewhere; the scalar synchronization algebra alone provides no such ledger.

## Scale/type check

- The theorem is dimensionless finite amplitude algebra.
- It does not identify `a,b` with Fourier coefficients of an actual velocity.
- It does not commute synchronization with Leray projection or the quadratic
  Euler interaction.
- It does not cross finite replicas to infinitely many packet generations.
- It does not contradict the global energy inequality; rather, it proves that
  a proposed reduced map cannot inherit that inequality without additional
  modes and dissipation.

## Assumptions

- Real amplitudes and the displayed symmetric linear coupling.
- Euclidean energy `a^2+b^2`.
- Strict tangent gain `g>1` for the no-contraction conclusion.

## Critic verdict

🟢 PROVED for the exact replicated-amplitude architecture.

🟡 CONDITIONAL for Navier--Stokes: an anisotropic PDE construction could evade
the obstruction, but must exhibit the missing physical energy transfer.

## Lean status

- 🔵 LEAN-SOURCE: `verification/b2-round41/NSAnisotropicEnergyTax.lean`.
- ✅ LEAN-VERIFIED: NO; no clean kernel replay is claimed here.

## Exact remaining gap

🚧 MISSING — a divergence-free/helical packet realization for which transverse
contraction, tangent amplification, total PDE energy balance, viscosity,
pressure, transport, deformation, and recursive scale generation are proved
uniformly in the full three-dimensional equations.

## Provenance

- Internal survivor:
  `verification/ns-replicated-amplifier/NSReplicatedAmplifierFirewall.lean`,
  branch `agent/ns-replicated-amplifier-verifier-20260813`, head
  `9ab38378ff3b9de106d35fe844a2a6a55ad2be55`.
- Current comparison point: Stan Palasek, “Finite-time blow-up in an elementary
  model of the 3D Navier--Stokes equations,” arXiv:2605.13827 (2026), which is a
  shell-model result and discusses rather than proves an embedding into the
  full equations.
