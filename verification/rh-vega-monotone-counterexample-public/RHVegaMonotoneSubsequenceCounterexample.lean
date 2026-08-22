import Mathlib

/-!
Finite/infinite logical counterexample to the monotone-subsequence proposition
used in a 2026 claimed proof of RH.

The sequence `alt n = n % 2` has no strictly decreasing tail, but its range is
`{0,1}`, so it cannot contain three strictly increasing sampled values and hence
cannot contain an infinite strictly increasing subsequence.

This file says nothing about RH itself.
-/

namespace RHVegaMonotoneSubsequenceCounterexample

def alt (n : ℕ) : ℕ := n % 2

/-- Every value of the alternating sequence is at most one. -/
theorem alt_le_one (n : ℕ) : alt n ≤ 1 := by
  unfold alt
  omega

/-- After every cutoff there is a next step that is not strictly decreasing. -/
theorem no_strictly_decreasing_tail :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ¬ alt (n + 1) < alt n := by
  intro N
  refine ⟨2 * N, ?_, ?_⟩
  · omega
  · unfold alt
    simp

/-- Three values from the binary range cannot form a strict increasing chain. -/
theorem no_three_strictly_increasing_values
    (i j k : ℕ) :
    ¬ (alt i < alt j ∧ alt j < alt k) := by
  intro h
  have hk : alt k ≤ 1 := alt_le_one k
  omega

/-- Consequently no strictly increasing subsequence can have length three. -/
theorem no_length_three_strict_increasing_subsequence
    (s : Fin 3 → ℕ) :
    ¬ (alt (s 0) < alt (s 1) ∧ alt (s 1) < alt (s 2)) := by
  exact no_three_strictly_increasing_values (s 0) (s 1) (s 2)

/-- The two properties coexist, refuting the implication
`no strictly decreasing tail -> arbitrarily long strictly increasing chains`. -/
theorem proposition_counterexample :
    (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ¬ alt (n + 1) < alt n) ∧
    (∀ s : Fin 3 → ℕ,
      ¬ (alt (s 0) < alt (s 1) ∧ alt (s 1) < alt (s 2))) := by
  exact ⟨no_strictly_decreasing_tail,
    no_length_three_strict_increasing_subsequence⟩

#print axioms alt_le_one
#print axioms no_strictly_decreasing_tail
#print axioms no_three_strictly_increasing_values
#print axioms no_length_three_strict_increasing_subsequence
#print axioms proposition_counterexample

end RHVegaMonotoneSubsequenceCounterexample
