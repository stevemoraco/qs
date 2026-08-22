import Mathlib

/-!
# Yang--Mills audit: uniform Lipschitz continuity is not universality

Honesty status: elementary real analysis only. This file does not formalize
Yang--Mills theory, Osterwalder--Schrader reconstruction, regulator limits,
Schwinger functions, or any official Millennium statement.

It protects the exact logical obstruction used in the source audit: uniformly
Lipschitz, perfectly scale-stable families can have distinct scheme-dependent
limits. To deduce equality one needs a difference bound that actually vanishes,
not merely one that is finite or uniform in the scale.
-/

namespace MillenniumBraid
namespace YMUniversalityLipschitz

/-- A maximally simple scheme-dependent, scale-stable family. -/
def schemeValue (_scale : ℕ) (scheme : ℝ) : ℝ := scheme

/-- The family is uniformly 1-Lipschitz in the scheme parameter at every scale. -/
theorem schemeValue_uniform_lipschitz
    (scale : ℕ) (x y : ℝ) :
    |schemeValue scale x - schemeValue scale y| ≤ |x - y| := by
  simp [schemeValue]

/-- Every scheme has an exact scale-independent limiting value. -/
theorem schemeValue_exact_limit
    (scheme : ℝ) :
    ∃ limit : ℝ, ∀ scale : ℕ, schemeValue scale scheme = limit := by
  exact ⟨scheme, by intro scale; rfl⟩

/-- Distinct admissible parameters can retain distinct values at every scale. -/
theorem schemeValue_zero_one_distinct
    (scale : ℕ) :
    schemeValue scale 0 ≠ schemeValue scale 1 := by
  norm_num [schemeValue]

/--
Uniform Lipschitz control plus exact convergence of every parameterized sequence
does not imply parameter-independent limits.
-/
theorem uniform_lipschitz_convergent_family_need_not_be_universal :
    ∃ F : ℕ → ℝ → ℝ,
      (∀ scale x y,
        |F scale x - F scale y| ≤ |x - y|) ∧
      (∀ x, ∃ limit : ℝ, ∀ scale, F scale x = limit) ∧
      (∀ scale, F scale 0 ≠ F scale 1) := by
  refine ⟨schemeValue, ?_, ?_, ?_⟩
  · exact schemeValue_uniform_lipschitz
  · exact schemeValue_exact_limit
  · exact schemeValue_zero_one_distinct

/--
The correct scalar repair: equality follows if the limiting difference is
bounded by every positive tolerance. A merely finite bound is insufficient.
-/
theorem equality_of_vanishing_difference_bound
    (x y : ℝ)
    (hbound : ∀ ε : ℝ, 0 < ε → |x - y| ≤ ε) :
    x = y := by
  by_contra hne
  have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hhalf := hbound (|x - y| / 2) (half_pos hpos)
  linarith

#print axioms schemeValue_uniform_lipschitz
#print axioms schemeValue_exact_limit
#print axioms schemeValue_zero_one_distinct
#print axioms uniform_lipschitz_convergent_family_need_not_be_universal
#print axioms equality_of_vanishing_difference_bound

end YMUniversalityLipschitz
end MillenniumBraid
