import Mathlib

namespace SixLaneAudit.NSFiveDCriticalConcentration

/-- Spatial `L²` energy is scale invariant. -/
theorem spatial_l2_exponent :
    2 * ((5 : ℚ) / 2) - 5 = 0 := by
  norm_num

/-- Spacetime gradient energy is scale invariant. -/
theorem gradient_l2_spacetime_exponent :
    2 * (((5 : ℚ) / 2) + 1) - 5 - 2 = 0 := by
  norm_num

/-- The parabolic endpoint exponent is exactly `14/5`. -/
theorem critical_fourteen_fifths_exponent :
    ((14 : ℚ) / 5) * ((5 : ℚ) / 2) - 5 - 2 = 0 := by
  norm_num

/-- Spacetime `L²` gains two inverse powers. -/
theorem spacetime_l2_exponent :
    2 * ((5 : ℚ) / 2) - 5 - 2 = -2 := by
  norm_num

/-- Scaling uniquely forces the endpoint exponent. -/
theorem critical_exponent_unique {p : ℚ}
    (h : p * ((5 : ℚ) / 2) - 5 - 2 = 0) :
    p = (14 : ℚ) / 5 := by
  linarith

/-- Larger indices model smaller radii. -/
def radiusWorks (profile radiusIndex : ℕ) : Prop :=
  profile < radiusIndex

/-- Every profile has a profile-dependent radius. -/
theorem pointwise_profile_dependent_radius :
    ∀ profile : ℕ, ∃ radiusIndex : ℕ,
      radiusWorks profile radiusIndex := by
  intro profile
  exact ⟨profile + 1, Nat.lt_succ_self profile⟩

/-- No one radius works for every profile. -/
theorem no_uniform_radius :
    ¬ ∃ radiusIndex : ℕ, ∀ profile : ℕ,
      radiusWorks profile radiusIndex := by
  rintro ⟨radiusIndex, h⟩
  exact (Nat.lt_irrefl radiusIndex) (h radiusIndex)

/-- Exact finite quantifier-swap countermodel. -/
theorem pointwise_does_not_imply_uniform :
    (∀ profile : ℕ, ∃ radiusIndex : ℕ,
      radiusWorks profile radiusIndex) ∧
    ¬ (∃ radiusIndex : ℕ, ∀ profile : ℕ,
      radiusWorks profile radiusIndex) := by
  exact ⟨pointwise_profile_dependent_radius, no_uniform_radius⟩

#print axioms spatial_l2_exponent
#print axioms gradient_l2_spacetime_exponent
#print axioms critical_fourteen_fifths_exponent
#print axioms spacetime_l2_exponent
#print axioms critical_exponent_unique
#print axioms pointwise_profile_dependent_radius
#print axioms no_uniform_radius
#print axioms pointwise_does_not_imply_uniform

end SixLaneAudit.NSFiveDCriticalConcentration
