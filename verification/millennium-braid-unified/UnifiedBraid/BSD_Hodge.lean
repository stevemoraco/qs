import Mathlib

namespace MillenniumBraidUnified

namespace BSDCore

def scaleNat (n : ℕ) (x : ℤ) : ℤ := (n : ℤ) * x

theorem scaleNat_injective
    {n : ℕ} (hn : 0 < n) :
    Function.Injective (scaleNat n) := by
  intro x y hxy
  have hnZ : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hprod : (n : ℤ) * (x - y) = 0 := by
    dsimp [scaleNat] at hxy
    nlinarith
  rcases mul_eq_zero.mp hprod with hn0 | hsub
  · exact False.elim (hnZ hn0)
  · exact sub_eq_zero.mp hsub

theorem one_not_in_scaleNat_image
    {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ x : ℤ, scaleNat n x = 1 := by
  rintro ⟨x, hx⟩
  have hnZ : (2 : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast hn
  have hnnonneg : (0 : ℤ) ≤ (n : ℤ) := by
    linarith
  by_cases hxnonpos : x ≤ 0
  · have hmul : (n : ℤ) * x ≤ (n : ℤ) * 0 :=
      mul_le_mul_of_nonneg_left hxnonpos hnnonneg
    dsimp [scaleNat] at hx
    nlinarith
  · have hxpos : (1 : ℤ) ≤ x := by
      omega
    have hmul : (n : ℤ) * 1 ≤ (n : ℤ) * x :=
      mul_le_mul_of_nonneg_left hxpos hnnonneg
    dsimp [scaleNat] at hx
    nlinarith

theorem identical_lattices_admit_nonsaturated_comparisons
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ f : ℤ → ℤ,
      Function.Injective f ∧ ¬ Function.Surjective f := by
  refine ⟨scaleNat n, scaleNat_injective (lt_of_lt_of_le (by norm_num) hn), ?_⟩
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj 1
  exact one_not_in_scaleNat_image hn ⟨x, hx⟩

end BSDCore

namespace HodgeCore

theorem positive_and_negative_correspondence_codim_differ
    {n r : ℤ} (hr : 0 < r) : n + r ≠ n - r := by
  linarith

theorem equal_codim_forces_zero_degree
    {n r : ℤ} (h : n + r = n - r) : r = 0 := by
  linarith

end HodgeCore

end MillenniumBraidUnified
