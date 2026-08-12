import Mathlib

namespace B4Auto20Run3

theorem ns_mass_floor_controls_spike_square
    (η p A E : ℝ) (hη : 0 < η) (hp : η ≤ p)
    (hE : p * A ^ 2 ≤ E) :
    A ^ 2 ≤ E / η := by
  apply (le_div_iff₀ hη).2
  nlinarith [sq_nonneg A]

theorem ns_unit_energy_spike_family
    (A : ℝ) (hA : 1 < A) :
    let p : ℝ := 1 / A ^ 2
    0 < p ∧ p < 1 ∧ p * A ^ 2 = 1 := by
  dsimp
  have hApos : 0 < A := by linarith
  have hA2 : 1 < A ^ 2 := by nlinarith
  have hA2pos : 0 < A ^ 2 := by positivity
  constructor
  · positivity
  constructor
  · exact (div_lt_one hA2pos).2 hA2
  · field_simp [ne_of_gt hApos]

#print axioms B4Auto20Run3.ns_mass_floor_controls_spike_square
#print axioms B4Auto20Run3.ns_unit_energy_spike_family

end B4Auto20Run3
