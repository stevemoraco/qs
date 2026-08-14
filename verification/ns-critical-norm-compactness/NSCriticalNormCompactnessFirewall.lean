import Mathlib

namespace NSCriticalNormCompactnessFirewall

theorem invariant_renormalization_cannot_bound_unbounded_size
    (size renorm : ℕ → ℝ)
    (hinv : ∀ n, renorm n = size n)
    (hunbounded : ∀ M : ℝ, ∃ n : ℕ, M < size n) :
    ¬ ∃ M : ℝ, ∀ n : ℕ, renorm n ≤ M := by
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := hunbounded M
  rw [← hinv n] at hn
  exact (not_lt_of_ge (hM n)) hn

theorem invariant_renormalization_cannot_bound_divergent_nonnegative_size
    (size renorm : ℕ → ℝ)
    (hsize : ∀ n, 0 ≤ size n)
    (hinv : ∀ n, renorm n = size n)
    (hdiv : ∀ K : ℝ, 0 ≤ K → ∃ n : ℕ, K < size n) :
    ¬ ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, renorm n ≤ K := by
  rintro ⟨K, hK0, hK⟩
  obtain ⟨n, hn⟩ := hdiv K hK0
  rw [← hinv n] at hn
  exact (not_lt_of_ge (hK n)) hn

theorem route_failure_does_not_refute_target :
    ¬ (∀ Route Target : Prop, (Route → Target) → ¬ Route → ¬ Target) := by
  intro h
  have hfalse : ¬ True := h False True (fun hf => False.elim hf) (fun hf => hf)
  exact hfalse trivial

#print axioms invariant_renormalization_cannot_bound_unbounded_size
#print axioms invariant_renormalization_cannot_bound_divergent_nonnegative_size
#print axioms route_failure_does_not_refute_target

end NSCriticalNormCompactnessFirewall
