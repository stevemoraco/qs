import Mathlib

namespace Millennium.YangMills

theorem plaquette_defect_three_scalings (a : ℝ) (ha : a ≠ 0) :
    (1 - (1 - a^3)) / a^4 = 1 / a ∧
    (1 - (1 - a^4)) / a^4 = 1 ∧
    (1 - (1 - a^5)) / a^4 = a := by
  constructor
  · field_simp [ha]
    ring
  constructor
  · field_simp [ha]
    ring
  · field_simp [ha]
    ring

theorem inverse_scale_plaquette_defect_three_scalings
    (n : ℝ) (hn : n ≠ 0) :
    (1 - (1 - (1 / n)^3)) / (1 / n)^4 = n ∧
    (1 - (1 - (1 / n)^4)) / (1 / n)^4 = 1 ∧
    (1 - (1 - (1 / n)^5)) / (1 / n)^4 = 1 / n := by
  have hinv : (1 / n : ℝ) ≠ 0 := div_ne_zero one_ne_zero hn
  obtain ⟨h3, h4, h5⟩ := plaquette_defect_three_scalings (1 / n) hinv
  constructor
  · calc
      (1 - (1 - (1 / n)^3)) / (1 / n)^4 = 1 / (1 / n) := h3
      _ = n := by field_simp [hn]
  constructor
  · exact h4
  · exact h5

theorem third_order_normalized_defect_arbitrary_overshoot
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      C < (1 - (1 - a^3)) / a^4 := by
  let a : ℝ := 1 / (C + 2)
  have hden : 0 < C + 2 := by linarith
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have ha1 : a < 1 := by
    dsimp [a]
    rw [div_lt_one hden]
    linarith
  have hane : a ≠ 0 := ne_of_gt ha
  refine ⟨a, ha, ha1, ?_⟩
  have hscale := (plaquette_defect_three_scalings a hane).1
  rw [hscale]
  dsimp [a]
  have hrecip : 1 / (1 / (C + 2)) = C + 2 := by
    field_simp
  rw [hrecip]
  linarith

theorem fifth_order_normalized_defect_arbitrary_undershoot
    (eps : ℝ) (heps : 0 < eps) :
    ∃ a : ℝ, 0 < a ∧ a < eps ∧
      (1 - (1 - a^5)) / a^4 < eps := by
  let a : ℝ := eps / 2
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have haeps : a < eps := by
    dsimp [a]
    linarith
  have hane : a ≠ 0 := ne_of_gt ha
  refine ⟨a, ha, haeps, ?_⟩
  have hscale := (plaquette_defect_three_scalings a hane).2.2
  rw [hscale]
  exact haeps

#print axioms plaquette_defect_three_scalings
#print axioms inverse_scale_plaquette_defect_three_scalings
#print axioms third_order_normalized_defect_arbitrary_overshoot
#print axioms fifth_order_normalized_defect_arbitrary_undershoot

end Millennium.YangMills
