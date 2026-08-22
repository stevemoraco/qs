import Mathlib

namespace Millennium
namespace Round218PNP

def HasExponentBound (L k : ℕ) : Prop := L ≤ k

theorem every_language_has_some_exponent :
    ∀ L : ℕ, ∃ k : ℕ, HasExponentBound L k := by
  intro L
  exact ⟨L, le_rfl⟩

theorem every_exponent_misses_some_language :
    ∀ k : ℕ, ∃ L : ℕ, ¬ HasExponentBound L k := by
  intro k
  refine ⟨k + 1, ?_⟩
  simp [HasExponentBound]

theorem languagewise_bounds_compatible_with_no_uniform_exponent :
    ∃ C : ℕ → ℕ → Prop,
      (∀ L, ∃ k, C L k) ∧
      (∀ k, ∃ L, ¬ C L k) := by
  refine ⟨HasExponentBound, every_language_has_some_exponent, ?_⟩
  exact every_exponent_misses_some_language

theorem no_one_exponent_bounds_all_languages :
    ¬ ∃ k : ℕ, ∀ L : ℕ, HasExponentBound L k := by
  rintro ⟨k, hk⟩
  have hbad : HasExponentBound (k + 1) k := hk (k + 1)
  simp [HasExponentBound] at hbad

theorem three_n_below_quadratic
    (n : ℕ) (hn : 4 ≤ n) :
    3 * n < n ^ 2 := by
  nlinarith

theorem linear_sparse_hardwire_budget
    (n t : ℕ) (ht : t ≤ 7 * n) :
    t * (n + 1) ≤ 7 * n * (n + 1) := by
  exact Nat.mul_le_mul_right (n + 1) ht

theorem seven_n_hardwire_budget_expands (n : ℕ) :
    7 * n * (n + 1) = 7 * n ^ 2 + 7 * n := by
  ring

theorem near_linear_lower_and_quadratic_upper_consistent
    (n : ℕ) (hn : 4 ≤ n) :
    3 * n < 7 * n ^ 2 + 7 * n := by
  have h : 3 * n < n ^ 2 := three_n_below_quadratic n hn
  nlinarith

#print axioms every_language_has_some_exponent
#print axioms every_exponent_misses_some_language
#print axioms languagewise_bounds_compatible_with_no_uniform_exponent
#print axioms no_one_exponent_bounds_all_languages
#print axioms three_n_below_quadratic
#print axioms linear_sparse_hardwire_budget
#print axioms seven_n_hardwire_budget_expands
#print axioms near_linear_lower_and_quadratic_upper_consistent

end Round218PNP
end Millennium
