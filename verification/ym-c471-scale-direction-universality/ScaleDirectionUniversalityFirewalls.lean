import Mathlib

namespace Millennium.YangMills.C471

theorem coarse_and_refining_step_incompatible
    (a b next : ℝ)
    (ha : 0 < a)
    (hb : 1 < b)
    (hcoarse : next = b * a)
    (hrefine : next = a / b) : False := by
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  have hleft : a / b < a := by
    rw [div_lt_iff₀ hb0]
    nlinarith
  have hright : a < b * a := by
    nlinarith
  have heq : b * a = a / b := hcoarse.symm.trans hrefine
  linarith

theorem coarse_power_time_ne_refining_time
    (a b : ℝ) (ha : 0 < a) (hb : 1 < b) :
    b * a ≠ a / b := by
  intro h
  exact coarse_and_refining_step_incompatible a b (b * a) ha hb rfl h

theorem additive_error_iteration
    (d eps : ℕ → ℝ)
    (hstep : ∀ k, d (k + 1) ≤ d k + eps k) :
    ∀ n, d n ≤ d 0 + ∑ k in Finset.range n, eps k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        d (n + 1) ≤ d n + eps n := hstep n
        _ ≤ (d 0 + ∑ k in Finset.range n, eps k) + eps n :=
          add_le_add_right ih _
        _ = d 0 + ∑ k in Finset.range (n + 1), eps k := by
          rw [Finset.sum_range_succ]
          ring

theorem summable_additive_error_does_not_force_zero :
    ∃ d eps : ℕ → ℝ,
      (∀ k, d (k + 1) ≤ d k + eps k) ∧
      Summable eps ∧
      (∀ k, d k = 1) := by
  refine ⟨(fun _ => 1), (fun _ => 0), ?_, summable_zero, ?_⟩
  · intro k
    norm_num
  · intro k
    rfl

theorem finite_loss_without_reserve_can_close_gap :
    ∃ initial loss : ℝ,
      0 < initial ∧ 0 ≤ loss ∧ initial - loss = 0 := by
  exact ⟨1, 1, by norm_num⟩

theorem strict_reserve_preserves_positive_gap
    (initial loss reserve : ℝ)
    (hreserve : 0 < reserve)
    (hbudget : reserve ≤ initial - loss) :
    0 < initial - loss :=
  lt_of_lt_of_le hreserve hbudget

#print axioms coarse_and_refining_step_incompatible
#print axioms coarse_power_time_ne_refining_time
#print axioms additive_error_iteration
#print axioms summable_additive_error_does_not_force_zero
#print axioms finite_loss_without_reserve_can_close_gap
#print axioms strict_reserve_preserves_positive_gap

end Millennium.YangMills.C471
