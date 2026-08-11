import Mathlib

namespace PNP
namespace TorusSymmetrizationObstruction

def andHalf (x y : ℚ) : ℚ := x * y / 2

def asymmetricTorusP (x y : ℚ) : ℚ := y + x * y / 2

def swapAverage (x y : ℚ) : ℚ :=
  (asymmetricTorusP x y + asymmetricTorusP y x) / 2

def swapSum (x y : ℚ) : ℚ :=
  asymmetricTorusP x y + asymmetricTorusP y x

theorem exact_lift_00 :
    asymmetricTorusP 0 0 = 0 + andHalf 0 0 := by
  norm_num [asymmetricTorusP, andHalf]

theorem exact_lift_10 :
    asymmetricTorusP 1 0 = 0 + andHalf 1 0 := by
  norm_num [asymmetricTorusP, andHalf]

theorem exact_lift_01 :
    asymmetricTorusP 0 1 = 1 + andHalf 0 1 := by
  norm_num [asymmetricTorusP, andHalf]

theorem exact_lift_11 :
    asymmetricTorusP 1 1 = 1 + andHalf 1 1 := by
  norm_num [asymmetricTorusP, andHalf]

theorem swapAverage_at_10 :
    swapAverage 1 0 = 1 / 2 := by
  norm_num [swapAverage, asymmetricTorusP]

theorem no_integer_lift_for_swapAverage_at_10 :
    ¬ ∃ z : ℤ,
      |swapAverage 1 0 - ((z : ℚ) + andHalf 1 0)| < 1 / 4 := by
  rintro ⟨z, hz⟩
  norm_num [swapAverage, asymmetricTorusP, andHalf] at hz
  rw [abs_lt] at hz
  have hzCases : z ≤ 0 ∨ 1 ≤ z := by omega
  cases hzCases with
  | inl hzle =>
      have hzleQ : (z : ℚ) ≤ 0 := by exact_mod_cast hzle
      linarith
  | inr hzge =>
      have hzgeQ : (1 : ℚ) ≤ (z : ℚ) := by exact_mod_cast hzge
      linarith

theorem swapSum_at_11 :
    swapSum 1 1 = 3 := by
  norm_num [swapSum, asymmetricTorusP]

theorem no_integer_lift_for_swapSum_at_11 :
    ¬ ∃ z : ℤ,
      |swapSum 1 1 - ((z : ℚ) + andHalf 1 1)| < 1 / 4 := by
  rintro ⟨z, hz⟩
  norm_num [swapSum, asymmetricTorusP, andHalf] at hz
  rw [abs_lt] at hz
  have hzCases : z ≤ 2 ∨ 3 ≤ z := by omega
  cases hzCases with
  | inl hzle =>
      have hzleQ : (z : ℚ) ≤ 2 := by exact_mod_cast hzle
      linarith
  | inr hzge =>
      have hzgeQ : (3 : ℚ) ≤ (z : ℚ) := by exact_mod_cast hzge
      linarith

theorem even_multiplicity_annihilates_half_phase
    (k t : ℤ)
    (hk : k = 2 * t) :
    (k : ℚ) * (1 / 2) = (t : ℚ) := by
  subst k
  norm_num

theorem average_of_integer_lifts_need_not_be_integer :
    ¬ ∃ z : ℤ, ((z : ℚ) = (0 + 1) / 2) := by
  rintro ⟨z, hz⟩
  norm_num at hz
  have hzCases : z ≤ 0 ∨ 1 ≤ z := by omega
  cases hzCases with
  | inl hzle =>
      have hzleQ : (z : ℚ) ≤ 0 := by exact_mod_cast hzle
      linarith
  | inr hzge =>
      have hzgeQ : (1 : ℚ) ≤ (z : ℚ) := by exact_mod_cast hzge
      linarith

#print axioms exact_lift_00
#print axioms exact_lift_10
#print axioms exact_lift_01
#print axioms exact_lift_11
#print axioms swapAverage_at_10
#print axioms no_integer_lift_for_swapAverage_at_10
#print axioms swapSum_at_11
#print axioms no_integer_lift_for_swapSum_at_11
#print axioms even_multiplicity_annihilates_half_phase
#print axioms average_of_integer_lifts_need_not_be_integer

end TorusSymmetrizationObstruction
end PNP
