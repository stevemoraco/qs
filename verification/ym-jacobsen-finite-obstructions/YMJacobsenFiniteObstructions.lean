import Mathlib

namespace YM
namespace JacobsenFiniteObstructions

theorem activity_floor_from_half_boltzmann
    (w : ℝ)
    (hw : w ≤ 1 / 2) :
    1 / 2 ≤ |w - 1| := by
  rw [abs_of_nonpos]
  · linarith
  · linarith

theorem first_polymer_factor_exceeds_one
    (activity : ℝ)
    (hactivity : 1 / 2 ≤ activity) :
    1 < 12 * activity := by
  linarith

theorem half_boltzmann_kills_twelve_fold_smallness
    (w : ℝ)
    (hw : w ≤ 1 / 2) :
    1 < 12 * |w - 1| := by
  exact first_polymer_factor_exceeds_one _
    (activity_floor_from_half_boltzmann w hw)

theorem wilson_endpoint_exponent_coupling_identity
    (g2 : ℝ)
    (hg2 : g2 ≠ 0) :
    ((6 / g2) / 3) * (9 / 2) = 9 / g2 := by
  field_simp
  ring

theorem claimed_kk_factor_at_zero_spacing
    (c g5sq : ℝ) :
    Real.exp (-c * (6 * 0 / g5sq)) = 1 := by
  simp

def quartic2 (x y : ℚ) : ℚ := x ^ 4 + y ^ 4

theorem quartic2_swap (x y : ℚ) :
    quartic2 y x = quartic2 x y := by
  simp [quartic2, add_comm]

theorem quartic2_sign_left (x y : ℚ) :
    quartic2 (-x) y = quartic2 x y := by
  simp [quartic2]

theorem rational_points_same_radius :
    (1 : ℚ) ^ 2 + 0 ^ 2 = (3 / 5 : ℚ) ^ 2 + (4 / 5 : ℚ) ^ 2 := by
  norm_num

theorem quartic2_not_radial_on_equal_radius_points :
    quartic2 1 0 ≠ quartic2 (3 / 5) (4 / 5) := by
  norm_num [quartic2]

theorem hypercubic_invariance_does_not_force_radiality :
    ∃ f : ℚ → ℚ → ℚ,
      (∀ x y, f y x = f x y) ∧
      (∀ x y, f (-x) y = f x y) ∧
      ((1 : ℚ) ^ 2 + 0 ^ 2 = (3 / 5 : ℚ) ^ 2 + (4 / 5 : ℚ) ^ 2) ∧
      f 1 0 ≠ f (3 / 5) (4 / 5) := by
  refine ⟨quartic2, quartic2_swap, quartic2_sign_left, ?_, ?_⟩
  · exact rational_points_same_radius
  · exact quartic2_not_radial_on_equal_radius_points

theorem scaled_vacuum_power_exceeds_one
    (q : ℝ)
    (hq : 1 < q)
    (N : ℕ)
    (hN : 0 < N) :
    1 < q ^ N := by
  exact one_lt_pow₀ hq hN

#print axioms activity_floor_from_half_boltzmann
#print axioms first_polymer_factor_exceeds_one
#print axioms half_boltzmann_kills_twelve_fold_smallness
#print axioms wilson_endpoint_exponent_coupling_identity
#print axioms claimed_kk_factor_at_zero_spacing
#print axioms quartic2_swap
#print axioms quartic2_sign_left
#print axioms rational_points_same_radius
#print axioms quartic2_not_radial_on_equal_radius_points
#print axioms hypercubic_invariance_does_not_force_radiality
#print axioms scaled_vacuum_power_exceeds_one

end JacobsenFiniteObstructions
end YM
