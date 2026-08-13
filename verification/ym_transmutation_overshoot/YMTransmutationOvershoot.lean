import Mathlib

namespace YMTransmutationOvershoot

/-- A vector recovered as a strong limit cannot simultaneously converge strongly to zero. -/
theorem eq_zero_of_recovery_and_vanishing
    {E : Type*} [NormedAddCommGroup E]
    (u : ℕ → E) (x : E)
    (hrecover : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖u n - x‖ < ε)
    (hvanish : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖u n‖ < ε) :
    x = 0 := by
  by_contra hx
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let ε : ℝ := ‖x‖ / 3
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  rcases hrecover ε hε with ⟨N₁, hN₁⟩
  rcases hvanish ε hε with ⟨N₂, hN₂⟩
  let n : ℕ := max N₁ N₂
  have hrec : ‖u n - x‖ < ε := hN₁ n (le_max_left _ _)
  have hsmall : ‖u n‖ < ε := hN₂ n (le_max_right _ _)
  have htri : ‖x‖ ≤ ‖u n - x‖ + ‖u n‖ := by
    have h := norm_add_le (x - u n) (u n)
    rw [sub_add_cancel, norm_sub_rev] at h
    exact h
  dsimp [ε] at hrec hsmall
  linarith

/-- Pointwise strong convergence plus pointwise convergence to zero forces the limit map to be zero. -/
theorem strong_limit_map_eq_zero
    {E : Type*} [NormedAddCommGroup E]
    (Areg : ℕ → E → E) (Alim : E → E)
    (hstrong : ∀ x ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖Areg n x - Alim x‖ < ε)
    (hvanish : ∀ x ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖Areg n x‖ < ε) :
    ∀ x, Alim x = 0 := by
  intro x
  exact eq_zero_of_recovery_and_vanishing
    (u := fun n => Areg n x) (x := Alim x)
    (hrecover := hstrong x) (hvanish := hvanish x)

/-- If every positive-time map is zero on a sector and the maps recover the identity at time zero,
then the sector map is zero. -/
theorem zero_sector_of_zero_maps_and_recovery
    {E : Type*} [NormedAddCommGroup E]
    (Q : E → E) (U : ℕ → E → E)
    (hzero : ∀ k x, U k (Q x) = 0)
    (hrecover : ∀ x ε : ℝ, 0 < ε →
      ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ‖U k (Q x) - Q x‖ < ε) :
    ∀ x, Q x = 0 := by
  intro x
  apply eq_zero_of_recovery_and_vanishing
    (u := fun k => U k (Q x)) (x := Q x)
  · exact hrecover x
  · intro ε hε
    refine ⟨0, ?_⟩
    intro k hk
    simp [hzero]

/-- Abstract two-limit core of the transmutation-overshoot zero-sector theorem. -/
theorem overshoot_zero_sector_core
    {E : Type*} [NormedAddCommGroup E]
    (Areg : ℕ → ℕ → E → E)
    (Alim : ℕ → E → E)
    (Q : E → E)
    (hstrong : ∀ k x ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖Areg k n x - Alim k x‖ < ε)
    (hvanish : ∀ k x ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖Areg k n x‖ < ε)
    (hrecover : ∀ x ε : ℝ, 0 < ε →
      ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ‖Alim k (Q x) - Q x‖ < ε) :
    ∀ x, Q x = 0 := by
  have hzero : ∀ k x, Alim k x = 0 := by
    intro k
    exact strong_limit_map_eq_zero
      (Areg := Areg k) (Alim := Alim k)
      (hstrong := hstrong k) (hvanish := hvanish k)
  exact zero_sector_of_zero_maps_and_recovery Q Alim hzero hrecover

/-- Finite weighted recurrence telescoping behind preservation of `M / Λ`. -/
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

/-- A lower and upper comparison with one positive scale is exactly a two-sided ratio window. -/
theorem two_sided_scale_window
    {mass scale lower upper : ℝ}
    (hscale : 0 < scale)
    (hlower : lower * scale ≤ mass)
    (hupper : mass ≤ upper * scale) :
    lower ≤ mass / scale ∧ mass / scale ≤ upper := by
  constructor
  · exact (le_div_iff₀ hscale).2 hlower
  · exact (div_le_iff₀ hscale).2 hupper

#print axioms eq_zero_of_recovery_and_vanishing
#print axioms strong_limit_map_eq_zero
#print axioms zero_sector_of_zero_maps_and_recovery
#print axioms overshoot_zero_sector_core
#print axioms weighted_recurrence_telescopes
#print axioms two_sided_scale_window

end YMTransmutationOvershoot
