import Mathlib

namespace RHSelectorPositivePart

open Finset

/-- Every bounded selector is dominated by the positive part, pointwise after
multiplication by a nonnegative weight. -/
theorem weighted_selector_le_positive_part
    {ι : Type*} [Fintype ι]
    (w f theta : ι -> ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (htheta0 : ∀ i, 0 ≤ theta i)
    (htheta1 : ∀ i, theta i ≤ 1) :
    (∑ i, w i * theta i * f i) ≤ ∑ i, w i * max (f i) 0 := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases hf : 0 ≤ f i
  · rw [max_eq_left hf]
    have htf : theta i * f i ≤ 1 * f i :=
      mul_le_mul_of_nonneg_right (htheta1 i) hf
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left htf (hw i)
  · have hf' : f i ≤ 0 := le_of_not_ge hf
    rw [max_eq_right hf']
    have htf : theta i * f i ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (htheta0 i) hf'
    simpa [mul_assoc] using mul_nonpos_of_nonneg_of_nonpos (hw i) htf

/-- The indicator of the positive set attains the positive-part bound. -/
theorem positive_selector_attains
    {ι : Type*} [Fintype ι]
    (w f : ι -> ℝ) :
    let theta : ι -> ℝ := fun i => if 0 < f i then 1 else 0
    (∀ i, 0 ≤ theta i) ∧
    (∀ i, theta i ≤ 1) ∧
    (∑ i, w i * theta i * f i) = ∑ i, w i * max (f i) 0 := by
  dsimp
  constructor
  · intro i
    split <;> norm_num
  constructor
  · intro i
    split <;> norm_num
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases hf : 0 < f i
    · simp [hf, max_eq_left hf.le]
    · have hf' : f i ≤ 0 := le_of_not_gt hf
      simp [hf, max_eq_right hf']

/-- Uniform control against all selectors `0 ≤ theta ≤ 1` is exactly control
of the weighted positive excess. -/
theorem all_selectors_iff_positive_part
    {ι : Type*} [Fintype ι]
    (w f : ι -> ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (E : ℝ) :
    (∀ theta : ι -> ℝ,
      (∀ i, 0 ≤ theta i) ->
      (∀ i, theta i ≤ 1) ->
      (∑ i, w i * theta i * f i) ≤ E) ↔
      (∑ i, w i * max (f i) 0) ≤ E := by
  constructor
  · intro hall
    let theta : ι -> ℝ := fun i => if 0 < f i then 1 else 0
    have hattain := positive_selector_attains w f
    dsimp only at hattain
    rw [← hattain.2.2]
    exact hall theta hattain.1 hattain.2.1
  · intro hpos theta htheta0 htheta1
    exact (weighted_selector_le_positive_part w f theta hw htheta0 htheta1).trans hpos

/-- Negativity of an antitone aperture floor persists at every larger aperture. -/
theorem negative_persists_of_antitone
    {f : ℝ -> ℝ} (hf : Antitone f)
    {a b : ℝ} (hab : a ≤ b) (ha : f a < 0) :
    f b < 0 := by
  exact lt_of_le_of_lt (hf hab) ha

#print axioms weighted_selector_le_positive_part
#print axioms positive_selector_attains
#print axioms all_selectors_iff_positive_part
#print axioms negative_persists_of_antitone

end RHSelectorPositivePart
