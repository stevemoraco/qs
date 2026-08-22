import Mathlib

namespace NSStationarityFirewall

theorem value_saturation_does_not_force_stationarity :
    ∃ (J A : ℝ → ℝ) (Λ : ℝ),
      J 1 = Λ * A 1 ∧
      HasDerivAt (fun a => J a - Λ * A a) 1 1 := by
  refine ⟨(fun a : ℝ => a), (fun _ : ℝ => 1), 1, ?_, ?_⟩
  · norm_num
  · have h : HasDerivAt (fun a : ℝ => a - 1) 1 1 := by
      simpa using (hasDerivAt_id (x := (1 : ℝ))).sub_const (1 : ℝ)
    simpa using h

theorem bare_value_to_zero_variation_is_false :
    ¬ (∀ (J A : ℝ → ℝ) (Λ : ℝ),
        J 1 = Λ * A 1 →
        HasDerivAt (fun a => J a - Λ * A a) 0 1) := by
  intro hall
  have hs := hall (fun a : ℝ => a) (fun _ : ℝ => 1) 1 (by norm_num)
  have hs' : HasDerivAt (fun a : ℝ => a - 1) 0 1 := by
    simpa using hs
  have htrue : HasDerivAt (fun a : ℝ => a - 1) 1 1 := by
    simpa using (hasDerivAt_id (x := (1 : ℝ))).sub_const (1 : ℝ)
  have hbad : (0 : ℝ) = 1 := hs'.unique htrue
  norm_num at hbad

#print axioms value_saturation_does_not_force_stationarity
#print axioms bare_value_to_zero_variation_is_false

end NSStationarityFirewall
