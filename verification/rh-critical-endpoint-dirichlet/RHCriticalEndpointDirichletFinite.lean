import Mathlib

namespace RHCriticalEndpointDirichlet

/-- The magnitude of the negative excursion of a real scalar. -/
def negPart (x : ℝ) : ℝ := max (-x) 0

/-- Negative excursion is nonnegative. -/
theorem negPart_nonneg (x : ℝ) : 0 ≤ negPart x := by
  exact le_max_right (-x) 0

/-- A larger scalar response has a smaller negative excursion. -/
theorem negPart_anti {a b : ℝ} (h : a ≤ b) :
    negPart b ≤ negPart a := by
  unfold negPart
  exact max_le_max (neg_le_neg h) le_rfl

/-- The negative part is bounded by the absolute value. -/
theorem negPart_le_abs (x : ℝ) : negPart x ≤ |x| := by
  unfold negPart
  exact max_le (neg_le_abs x) (abs_nonneg x)

/-- If the unconstrained root response lies below the clamped response and its
absolute value has a majorant, the same majorant controls the clamped negative
part.  This is the finite order spine of the envelope-independent endpoint
argument. -/
theorem clamped_negPart_le_majorant
    {root clamped majorant : ℝ}
    (hroot : root ≤ clamped)
    (hmajorant : |root| ≤ majorant) :
    negPart clamped ≤ majorant := by
  exact le_trans (negPart_anti hroot)
    (le_trans (negPart_le_abs root) hmajorant)

/-- Cross-multiplied critical-weight cancellation.  If a numerator is bounded
by `s * w`, then after multiplying by the positive square denominator the
critical `s^3` versus `s^2` weight comparison is exact. -/
theorem critical_sqrt_weight_cross
    (s numerator weight : ℝ)
    (hbound : numerator ≤ s * weight) :
    numerator * s ^ 2 ≤ weight * s ^ 3 := by
  have hsq : 0 ≤ s ^ 2 := sq_nonneg s
  have hmul := mul_le_mul_of_nonneg_right hbound hsq
  nlinarith

/-- The square and cube denominators used by the critical endpoint are positive
when the square-root variable is positive. -/
theorem critical_denominators_pos
    {s : ℝ} (hs : 0 < s) :
    0 < s ^ 2 ∧ 0 < s ^ 3 := by
  exact ⟨pow_pos hs 2, pow_pos hs 3⟩

/-- Abstract removal of the first two reciprocal tests.  Once tests `1` and `2`
are unconditional, a criterion quantified over all positive indices is
identical to the tail criterion beginning at index `3`. -/
theorem drop_first_two_reciprocal_tests
    {P : Prop} (Z : ℕ → Prop)
    (hcriterion : P ↔ ∀ n : ℕ, 1 ≤ n → Z n)
    (hZ1 : Z 1)
    (hZ2 : Z 2) :
    P ↔ ∀ n : ℕ, 3 ≤ n → Z n := by
  constructor
  · intro hP n hn
    exact (hcriterion.mp hP) n (by omega)
  · intro htail
    apply hcriterion.mpr
    intro n hn
    by_cases hn1 : n = 1
    · subst n
      exact hZ1
    by_cases hn2 : n = 2
    · subst n
      exact hZ2
    exact htail n (by omega)

/-- If every reciprocal test from index three onward converges and a false
case always forces a failure at some index at least three, then the tail is
already a terminal criterion. -/
theorem tail_tests_force_target
    {P : Prop} (Z : ℕ → Prop)
    (hfalse : ¬ P → ∃ n : ℕ, 3 ≤ n ∧ ¬ Z n)
    (htail : ∀ n : ℕ, 3 ≤ n → Z n) :
    P := by
  by_contra hP
  rcases hfalse hP with ⟨n, hn, hbad⟩
  exact hbad (htail n hn)

#print axioms negPart_nonneg
#print axioms negPart_anti
#print axioms negPart_le_abs
#print axioms clamped_negPart_le_majorant
#print axioms critical_sqrt_weight_cross
#print axioms critical_denominators_pos
#print axioms drop_first_two_reciprocal_tests
#print axioms tail_tests_force_target

end RHCriticalEndpointDirichlet
