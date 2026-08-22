import Mathlib

namespace NSEnergyPairGate

/-- Abstract algebraic core of the incompressible trilinear skew symmetry.
`b a x y = - b a y x` is the only structural hypothesis needed here. -/
theorem skew_self_zero
    {V : Type*}
    (b : V → V → V → ℝ)
    (hskew : ∀ a x y, b a x y = - b a y x)
    (a x : V) :
    b a x x = 0 := by
  have h := hskew a x x
  linarith

/-- One adjacent trilinear coefficient determines both energy-paired shell
coefficients. If `c = b ψ ψ φ`, then skewness in the last two slots gives
`b ψ φ ψ = -c`, while the self term `b φ ψ ψ` vanishes. -/
theorem paired_coefficient
    {V : Type*}
    (b : V → V → V → ℝ)
    (hskew : ∀ a x y, b a x y = - b a y x)
    (φ ψ : V)
    (c : ℝ)
    (hc : b ψ ψ φ = c) :
    b φ ψ ψ = 0 ∧ b ψ φ ψ = -c := by
  constructor
  · exact skew_self_zero b hskew φ ψ
  · calc
      b ψ φ ψ = - b ψ ψ φ := hskew ψ φ ψ
      _ = -c := by rw [hc]

/-- The induced two-shell quadratic energy transfer cancels exactly:
low contribution `-c Y²` plus high contribution `+c X Y`, weighted by
amplitudes `X` and `Y`, has zero total energy derivative. -/
theorem paired_energy_cancel
    (c X Y : ℝ) :
    X * (-c * Y ^ 2) + Y * (c * X * Y) = 0 := by
  ring

/-- Algebraic form of the Galerkin nonlinear pair in the sign convention
`u_t + B(u,u)=...`: a low equation contribution `-c Y²` forces the
energy-paired high contribution `+c X Y`. -/
theorem palasek_pair_energy_identity
    (c X Y : ℝ) :
    X * (-c * Y ^ 2) = - Y * (c * X * Y) := by
  ring

#print axioms skew_self_zero
#print axioms paired_coefficient
#print axioms paired_energy_cancel
#print axioms palasek_pair_energy_identity

end NSEnergyPairGate
