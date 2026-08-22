import Mathlib

namespace RHClampedNegativeDepth

/-- The magnitude of the negative excursion of a real number. -/
def negPart (x : ℝ) : ℝ := max (-x) 0

/-- Negative excursion is nonnegative. -/
theorem negPart_nonneg (x : ℝ) : 0 ≤ negPart x := by
  exact le_max_right (-x) 0

/-- A larger response has a smaller negative excursion. -/
theorem negPart_anti {a b : ℝ} (h : a ≤ b) :
    negPart b ≤ negPart a := by
  unfold negPart
  exact max_le_max (neg_le_neg h) le_rfl

/-- The two-sided negative-excursion consequence of a scalar sandwich. -/
theorem negPart_sandwich {lower middle upper : ℝ}
    (hlm : lower ≤ middle) (hmu : middle ≤ upper) :
    negPart upper ≤ negPart middle ∧
    negPart middle ≤ negPart lower := by
  exact ⟨negPart_anti hmu, negPart_anti hlm⟩

/-- A recursive floor for the finite prefix `u 0, ..., u (N-1)`, with zero
included so that the floor is always nonpositive. -/
def prefixFloor (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => min (prefixFloor u n) (u n)

/-- The recursive prefix floor is nonpositive. -/
theorem prefixFloor_nonpos (u : ℕ → ℝ) (N : ℕ) :
    prefixFloor u N ≤ 0 := by
  induction N with
  | zero => simp [prefixFloor]
  | succ N ih =>
      rw [prefixFloor]
      exact le_trans (min_le_left _ _) ih

/-- Every entry in a finite prefix lies above the recursive prefix floor. -/
theorem prefixFloor_le (u : ℕ → ℝ) {k N : ℕ} (hk : k < N) :
    prefixFloor u N ≤ u k := by
  induction N generalizing k with
  | zero => omega
  | succ N ih =>
      by_cases hEq : k = N
      · subst k
        simp [prefixFloor]
      · have hkN : k < N := by omega
        rw [prefixFloor]
        exact le_trans (min_le_left _ _) (ih hkN)

/-- A sequence is lower bounded in the elementary pointwise sense. -/
def LowerBounded (u : ℕ → ℝ) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ, B ≤ u n

/-- Eventual nonnegativity already implies a global lower bound, because only
finitely many initial values remain. -/
theorem eventually_nonneg_lowerBounded {u : ℕ → ℝ} {N : ℕ}
    (h : ∀ n : ℕ, N ≤ n → 0 ≤ u n) :
    LowerBounded u := by
  refine ⟨prefixFloor u N, ?_⟩
  intro n
  by_cases hn : n < N
  · exact prefixFloor_le u hn
  · have hN : N ≤ n := by omega
    exact le_trans (prefixFloor_nonpos u N) (h n hN)

/-- Abstract bounded-below criterion: if the target proposition gives eventual
nonnegativity, while its failure gives negative excursions below every fixed
floor, then the proposition is equivalent to lower boundedness. -/
theorem lowerBounded_criterion
    {P : Prop} {u : ℕ → ℝ}
    (hforward : P → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 ≤ u n)
    (hfalse : ¬ P → ∀ B : ℝ, ∃ n : ℕ, u n < B) :
    P ↔ LowerBounded u := by
  constructor
  · intro hP
    rcases hforward hP with ⟨N, hN⟩
    exact eventually_nonneg_lowerBounded hN
  · intro hbound
    by_contra hP
    rcases hbound with ⟨B, hB⟩
    rcases hfalse hP B with ⟨n, hn⟩
    exact (not_lt_of_ge (hB n)) hn

/-- In the zeta strip `0 ≤ delta ≤ 1/2`, the square-rebate exponent does not
exceed the main obstruction exponent. -/
theorem square_rebate_depth_le {delta : ℝ} (hdelta : delta ≤ 1 / 2) :
    2 * delta - 1 / 2 ≤ delta := by
  linarith

/-- For every synthetic staircase exponent below one, the clamp-rebate
exponent is strictly lower than the leading negative-excursion exponent. -/
theorem synthetic_rebate_lower_order {beta : ℝ} (hbeta : beta < 1) :
    2 * beta - 3 / 2 < beta - 1 / 2 := by
  linarith

/-- A synthetic exponent to the right of one half produces a positive
negative-excursion depth. -/
theorem synthetic_negative_depth_positive {beta : ℝ}
    (hbeta : 1 / 2 < beta) :
    0 < beta - 1 / 2 := by
  linarith

#print axioms negPart_nonneg
#print axioms negPart_anti
#print axioms negPart_sandwich
#print axioms prefixFloor_nonpos
#print axioms prefixFloor_le
#print axioms eventually_nonneg_lowerBounded
#print axioms lowerBounded_criterion
#print axioms square_rebate_depth_le
#print axioms synthetic_rebate_lower_order
#print axioms synthetic_negative_depth_positive

end RHClampedNegativeDepth
