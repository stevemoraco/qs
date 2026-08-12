import Mathlib
namespace B4Auto20Run2

theorem ns_mass_floor_lower_bounds_coefficient
    (η p a b : ℝ)
    (hηp : η ≤ p) (hpη : p ≤ 1 - η) (hab : a ≤ b) :
    2 * η * (1 - η) * (b - a) ≤ 2 * p * (1 - p) * (b - a) := by
  have hleft : 0 ≤ p - η := sub_nonneg.mpr hηp
  have hright : 0 ≤ 1 - η - p := by linarith
  have hprod : 0 ≤ (p - η) * (1 - η - p) := mul_nonneg hleft hright
  have hcoeff : η * (1 - η) ≤ p * (1 - p) := by
    nlinarith
  have hgap : 0 ≤ b - a := sub_nonneg.mpr hab
  have hmul := mul_le_mul_of_nonneg_right hcoeff hgap
  nlinarith

theorem ns_coefficient_below_epsilon
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    let p := ε / 4
    0 < p ∧ p < 1 ∧ 2 * p * (1 - p) < ε := by
  dsimp
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith [sq_nonneg ε]

#print axioms ns_mass_floor_lower_bounds_coefficient
#print axioms ns_coefficient_below_epsilon
end B4Auto20Run2
