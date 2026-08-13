import Mathlib

/-!
Finite algebraic core of the axial-reflection symmetry used for the
Albritton–Ożański vortex-column Rayleigh coefficients.

This does not formalize their PDE theorem or Navier–Stokes.
-/

namespace NS
namespace AOAxialReflection

/-- The characteristic phase `beta * W - Omega` is invariant when both the
axial velocity and helical ratio change sign. -/
theorem lambda_invariant (β W Ω : ℝ) :
    (-β) * (-W) - Ω = β * W - Ω := by
  ring

/-- The numerator entering AO's `a` coefficient is invariant under
`(beta,q,W') -> (-beta,-q,-W')`. -/
theorem a_numerator_invariant (β q Wp r : ℝ) :
    (((-β) * r^2 + (-q)) * (-Wp)) = (β * r^2 + q) * Wp := by
  ring

/-- The signed rational factor entering AO's `b` coefficient is invariant when
`beta` and pitch `q` change sign together. -/
theorem b_ratio_invariant (β q : ℝ) (hq : q ≠ 0) :
    ((-β) * (1 - (-β) * (-q))) / (-q)
      = β * (1 - β * q) / q := by
  field_simp
  ring

/-- The positive denominator factor is unchanged by `beta -> -beta`. -/
theorem beta_square_denominator_invariant (β r : ℝ) :
    1 + (-β)^2 * r^2 = 1 + β^2 * r^2 := by
  ring

#print axioms lambda_invariant
#print axioms a_numerator_invariant
#print axioms b_ratio_invariant
#print axioms beta_square_denominator_invariant

end AOAxialReflection
end NS
