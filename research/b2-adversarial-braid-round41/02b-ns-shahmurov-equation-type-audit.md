# Navier--Stokes: equation-type and spectral-coverage audit of a 2026 claimed blow-up proof

Date: 2026-08-13

## Status

📚 SOURCE-VERIFIED against arXiv:2604.09949v1 as available on 2026-08-13.

🟢 PROVED equation-level and quantifier-domain obstructions.

🔴 REFUTED the claimed reduction and full inverse certificate as written.

🧱 OBSTRUCTION to promoting the manuscript to a Clay breakdown theorem.

This is not a proof of global regularity and not a solution of the official
Navier--Stokes problem.

## Claim under audit

Rishad Shahmurov, *Stable Finite-Time Singularity Formation for 3D
Navier--Stokes via 5D-Lifted Axisymmetric Reductions*, arXiv:2604.09949v1,
claims smooth finite-energy periodic data whose three-dimensional
incompressible Navier--Stokes solution forms a finite-time singularity.  The
argument uses a 5D-lifted scalar profile and an interval
Newton--Kantorovich certificate.

Three independent load-bearing failures are visible in the displayed source.

## 1. Physical incompressibility was replaced by an auxiliary 5D divergence law

For a three-dimensional axisymmetric velocity

`u = u^r e_r + u^theta e_theta + u^z e_z`,

the physical cylindrical incompressibility equation is

`partial_r u^r + u^r/r + partial_z u^z = 0`.          (3D)

The manuscript instead imposes on the same meridional components

`partial_r u^r + 3u^r/r + partial_z u^z = 0`.         (5D)

The coefficient `3/r` is appropriate for a radial divergence in four radial
dimensions, and the operator

`partial_r^2 + 3/r partial_r + partial_z^2`

can legitimately occur in a lifted scalar diffusion identity.  It does not
change the physical divergence constraint on the transport velocity.

Subtracting (3D) from (5D) gives

`2u^r/r = 0`.

Thus for every `r>0`, simultaneous validity forces `u^r=0`; then (3D) gives
`partial_z u^z=0`.  A nontrivial localized meridional field cannot satisfy both
laws.

The manuscript's streamfunction recovery

`u^r=-r^(-3) partial_z psi`,
`u^z= r^(-3) partial_r psi`

satisfies (5D) by construction.  Its scaled physical divergence is instead

`r(partial_r u^r+partial_z u^z)+u^r = -2u^r`,

which is generally nonzero.  Therefore a certified solution of the displayed
lifted profile equation is not yet a physical incompressible 3D velocity.

## 2. Swirl forcing was substituted for an independent vorticity state

The standard lifted variables have distinct types:

`F=u^theta/r`,
`G=omega^theta/r`.

The meridional velocity is recovered from `G`; meanwhile
`partial_z(F^2)` is a source term in the evolution equation for `G`.  The April
manuscript evolves only its swirl scalar `Omega=F`, but uses

`B(psi/rho^4)=partial_zeta(Omega^2)`

to recover the meridional flow instantaneously from `F` alone.  This deletes
the independent state `G` and replaces a forcing term by the state that it
forces.

The smallest state-space counterexample is the no-swirl sector: genuine smooth
axisymmetric no-swirl data may have `F=0` and nonzero azimuthal vorticity
`G`.  A recovery depending only on `partial_z(F^2)` sees zero and cannot
parameterize that state.  No invariant-manifold theorem identifying
`G=partial_z(F^2)` is derived.

A later June 2026 manuscript by the same author explicitly describes
`partial_z(F^2)` as the source in the lifted `G` equation, confirming the typed
distinction; that later manuscript is used here only as a variable dictionary,
not as authority for its own global-regularity claim.

## 3. The Newton--Kantorovich inverse leaves modes 451 through 1199 uncovered

The finite interval Jacobian is a `450 x 450` truncation, covering modes through
450.  The advertised tail coercivity proof defines its lower bound by an
infimum over `j>=1200`, but its conclusion is stated for the entire projection
`j>450`.

The implication

`for every j>=1200, lower(j)>=gamma`

therefore does not prove

`for every j>450, lower(j)>=gamma`.

The finite annulus

`451 <= j <= 1199`

lies in neither certificate.  The integer `j=451` is already a witness.  A
single small singular value or uncontrolled coupling in that block invalidates
the displayed full inverse norm.  A residual-tail bound through mode 900 does
not repair an inverse theorem for arbitrary perturbations.

The public package described in the manuscript also does not reproduce the raw
interval inputs and generators needed to reconstruct the residual and Jacobian
certificates; checking the final scalar Newton inequality from printed
constants cannot certify how those constants were obtained.

## Claimant, critic, rebuilder

### Claimant

A rigorously validated stationary lifted profile, reconstructed and
periodized, supplies a finite-time singularity for the physical three-dimensional
incompressible equations.

### Critic

Even a perfect numerical certificate for the displayed scalar operator would
certify a modified model unless both equation-type failures are repaired.  The
published numerical certificate is additionally incomplete across a nonempty
spectral block.  These are upstream failures, not cosmetic missing estimates.

### Rebuilder

The smallest credible repair is:

1. restore `G=omega^theta/r` as an independent unknown;
2. derive the coupled rescaled `(F,G)` system directly from physical 3D
   incompressibility;
3. recover the meridional velocity from `G` by the true 3D axisymmetric
   Biot--Savart/streamfunction relation;
4. certify a stationary profile of that coupled system;
5. cover modes `1..450`, `451..1199`, and `>=1200`, including cross-block
   operator norms or a rigorous Schur complement;
6. publish all raw interval inputs and replay code;
7. only then audit self-similar reconstruction, Liouville obstructions,
   periodic transfer, Leray projection, and the exact Clay data class.

## Scale and type checks

- Auxiliary 5D scalar diffusion is not physical 5D incompressibility of the
  3D transport field.
- A source in a vorticity equation is not the vorticity state.
- A finite residual spillover estimate is not an infinite-dimensional inverse.
- A fixed-point certificate for a modified PDE is not a theorem for the Clay
  PDE.
- Failure of this manuscript does not imply global regularity.

## Assumptions

- The equations are read literally from arXiv:2604.09949v1.
- `u^r,u^z` denote the physical radial and axial velocity components, as the
  manuscript claims.
- The finite inverse covers only its displayed 450-mode block, and the tail
  infimum covers only its displayed domain `j>=1200` absent another theorem.

## Critic verdict

🔴 REFUTED AS WRITTEN — the current manuscript does not establish a singular
solution of the physical three-dimensional incompressible Navier--Stokes
equations.

🟢 PROVED — the divergence mismatch and uncovered spectral annulus are exact.

🟡 CONDITIONAL — a fundamentally repaired coupled profile proof could remain a
research route.

## Lean status

- 🔵 LEAN-SOURCE:
  `verification/b2-round41/NSClaimTypeFirewall.lean` stages the scaled
  divergence contradiction and middle-mode witness.
- ✅ LEAN-VERIFIED: pending the branch-wide clean replay; no promotion is made
  in this note.
- The source file does not formalize cylindrical calculus, the manuscript,
  interval arithmetic, Newton--Kantorovich, or Navier--Stokes.

## Exact remaining gap

🚧 MISSING — a complete physical `(F,G)` derivation and a replayable
full-spectrum certificate, followed by all finite-to-infinite, self-similar,
periodic, and Clay-interface arrows.

## Provenance

- Primary manuscript: arXiv:2604.09949v1, 10 April 2026.
- Variable-dictionary cross-check: arXiv:2606.07869v1, 5 June 2026.
- Internal prior audits: `stevemoraco/RH` commits
  `c6d27cf340eb061f1b20df880ba26e0c8c585635`,
  `b68c7328083856372baa6d09487dd469d8363536`, and
  `963e6ef70df0dd18717ac796a42f102f3eba481a`.
