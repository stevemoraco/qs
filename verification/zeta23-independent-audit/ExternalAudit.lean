import Solution
import Solution.Multiplicity

open Complex

noncomputable section

/-- The comparator-facing nontrivial-zero predicate is definitionally Mathlib's zeta zero
inside the open critical strip. -/
theorem external_isNontrivialZero_shape (ρ : ℂ) :
    IsNontrivialZero ρ ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 :=
  Iff.rfl

/-- Multiplicity is definitionally the finite part of Mathlib's analytic order. -/
theorem external_zeroMult_shape (ρ : ℂ) :
    zeroMult ρ = (analyticOrderAt riemannZeta ρ).toNat :=
  rfl

/-- Exact trusted-shape replay of the unconditional dyadic two-thirds theorem. -/
theorem external_two_thirds_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  two_thirds_on_critical_line

/-- Exact trusted-shape replay of the multiplicity-aware simple-zero theorem. -/
theorem external_two_thirds_simple_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  two_thirds_simple_on_critical_line

#print axioms external_isNontrivialZero_shape
#print axioms external_zeroMult_shape
#print axioms external_two_thirds_on_critical_line
#print axioms external_two_thirds_simple_on_critical_line
