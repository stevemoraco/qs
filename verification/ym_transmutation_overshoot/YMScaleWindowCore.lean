import Mathlib

namespace YMScaleWindowCore

theorem common_limit_zero
    {E : Type*} [NormedAddCommGroup E]
    (u : ℕ → E) (x : E)
    (hrecover : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖u n - x‖ < ε)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖u n‖ < ε) :
    x = 0 := by
  by_contra hx
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let ε : ℝ := ‖x‖ / 3
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  rcases hrecover ε hε with ⟨N₁, hN₁⟩
  rcases hsmall ε hε with ⟨N₂, hN₂⟩
  let n : ℕ := max N₁ N₂
  have hrec : ‖u n - x‖ < ε := hN₁ n (le_max_left _ _)
  have hvan : ‖u n‖ < ε := hN₂ n (le_max_right _ _)
  have htri : ‖x‖ ≤ ‖u n - x‖ + ‖u n‖ := by
    have h := norm_add_le (x - u n) (u n)
    rw [sub_add_cancel, norm_sub_rev] at h
    exact h
  dsimp [ε] at hrec hvan
  linarith

theorem scale_window_limit_core
    {E : Type*} [NormedAddCommGroup E]
    (Areg : ℕ → ℕ → E → E)
    (Alim : ℕ → E → E)
    (Q : E → E)
    (hstrong : ∀ (k : ℕ) (x : E) (ε : ℝ), 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖Areg k n x - Alim k x‖ < ε)
    (hsmall : ∀ (k : ℕ) (x : E) (ε : ℝ), 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖Areg k n x‖ < ε)
    (hrecover : ∀ (x : E) (ε : ℝ), 0 < ε →
      ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ‖Alim k (Q x) - Q x‖ < ε) :
    ∀ x, Q x = 0 := by
  have hAlim : ∀ (k : ℕ) (x : E), Alim k x = 0 := by
    intro k x
    exact common_limit_zero
      (u := fun n => Areg k n x) (x := Alim k x)
      (hrecover := hstrong k x) (hsmall := hsmall k x)
  intro x
  apply common_limit_zero
    (u := fun k => Alim k (Q x)) (x := Q x)
  · exact hrecover x
  · intro ε hε
    refine ⟨0, ?_⟩
    intro k hk
    simpa [hAlim] using hε

theorem weighted_recurrence_telescopes
    (ratio err weight : ℕ → ℝ)
    (hstep : ∀ k,
      weight k * ratio k - weight k * err k ≤
        weight (k + 1) * ratio (k + 1)) :
    ∀ n,
      weight 0 * ratio 0 - ∑ k ∈ Finset.range n, weight k * err k ≤
        weight n * ratio n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hs := hstep n
      linarith

theorem two_sided_scale_window
    {mass scale lower upper : ℝ}
    (hscale : 0 < scale)
    (hlower : lower * scale ≤ mass)
    (hupper : mass ≤ upper * scale) :
    lower ≤ mass / scale ∧ mass / scale ≤ upper := by
  constructor
  · exact (le_div_iff₀ hscale).2 hlower
  · exact (div_le_iff₀ hscale).2 hupper

#print axioms common_limit_zero
#print axioms scale_window_limit_core
#print axioms weighted_recurrence_telescopes
#print axioms two_sided_scale_window

end YMScaleWindowCore
