import Mathlib

namespace NSMesocellWindow

theorem exists_mesocell_window {α b : ℝ} (hα : α < (5 : ℝ) / 2) (hb : 1 < b) :
    ∃ θ : ℝ, 0 < θ ∧ θ < b - 1 ∧ θ < b * (5 - 2 * α) / 3 := by
  have h1 : 0 < b - 1 := by linarith
  have h2 : 0 < b * (5 - 2 * α) / 3 := by
    have hbpos : 0 < b := by linarith
    have ha : 0 < 5 - 2 * α := by linarith
    positivity
  refine ⟨min (b - 1) (b * (5 - 2 * α) / 3) / 2, ?_, ?_, ?_⟩
  · have hm : 0 < min (b - 1) (b * (5 - 2 * α) / 3) := lt_min h1 h2
    linarith
  · have hm : min (b - 1) (b * (5 - 2 * α) / 3) ≤ b - 1 := min_le_left _ _
    linarith
  · have hm : min (b - 1) (b * (5 - 2 * α) / 3) ≤ b * (5 - 2 * α) / 3 := min_le_right _ _
    linarith

theorem explicit_mesocell_checkpoint :
    let α : ℝ := 9 / 4
    let b : ℝ := 11 / 10
    let θ : ℝ := 1 / 20
    0 < θ ∧ θ < b - 1 ∧ θ < b * (5 - 2 * α) / 3 ∧
    b - 1 - θ = 1 / 20 ∧ b * (5 - 2 * α) - 3 * θ = 2 / 5 := by
  norm_num

#print axioms exists_mesocell_window
#print axioms explicit_mesocell_checkpoint

end NSMesocellWindow
