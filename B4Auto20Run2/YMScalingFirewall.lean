import Mathlib
namespace B4Auto20Run2

theorem ym_linear_raw_bound_to_normalized
    (a g c Λ : ℝ) (ha : 0 < a)
    (hraw : a * (c * Λ) ≤ g) :
    c * Λ ≤ g / a := by
  exact (le_div_iff₀ ha).2 hraw

theorem ym_positive_gap_can_miss_linear_scale
    (c Λ : ℝ) (hc : 0 < c) (hΛ : 0 < Λ) :
    let a : ℝ := 1
    let g : ℝ := c * Λ / 2
    0 < a ∧ 0 < g ∧ g < a * (c * Λ) := by
  dsimp
  have hp : 0 < c * Λ := mul_pos hc hΛ
  constructor
  · norm_num
  constructor <;> nlinarith

#print axioms ym_linear_raw_bound_to_normalized
#print axioms ym_positive_gap_can_miss_linear_scale
end B4Auto20Run2
