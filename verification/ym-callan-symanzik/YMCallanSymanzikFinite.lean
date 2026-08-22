import Mathlib

/-!
# Yang–Mills Callan–Symanzik gap transport: finite algebra core

HONESTY BOUNDARY

This file formalizes only two scalar algebra interfaces used by the human note:

* a multiplicative field-renormalization factor does not change the exponential
  rate of a transported pure exponential, apart from the rescaled mass;
* a positive spectral carrier of weight `A` can change a normalized correlator
  by at most `A` at any fixed time when both component correlators lie in
  `[0,1]`.

It does not formalize the Callan–Symanzik PDE, characteristics, asymptotic
freedom, spectral measures, trace-class probes, Osterwalder–Schrader
reconstruction, Yang–Mills theory, or a mass gap.
-/

namespace MillenniumBraid
namespace YMCallanSymanzikFinite

/-- Exact finite-time logarithmic-rate identity for a transported exponential.
The correction from the positive multiplicative factor `Z` is `log Z / t`. -/
theorem transported_exponential_log_rate
    (Z lambda mass time : ℝ)
    (hZ : 0 < Z)
    (htime : time ≠ 0) :
    -(1 / time) *
        Real.log (Z * Real.exp (-(lambda * mass) * time)) =
      lambda * mass - Real.log Z / time := by
  rw [Real.log_mul hZ.ne' (Real.exp_ne_zero _), Real.log_exp]
  field_simp [htime]
  ring

/-- Exact algebraic displacement caused by adding a weighted second component
and renormalizing the total mass. -/
theorem normalized_mixture_difference
    (A x y : ℝ)
    (hden : 1 + A ≠ 0) :
    (x + A * y) / (1 + A) - x =
      A * (y - x) / (1 + A) := by
  field_simp [hden]
  ring

/-- If the two component correlator values lie at distance at most one, then a
nonnegative hidden carrier of weight `A` changes the normalized correlator by
at most `A`. -/
theorem normalized_mixture_difference_bound
    (A x y : ℝ)
    (hA : 0 ≤ A)
    (hxy : |y - x| ≤ 1) :
    |(x + A * y) / (1 + A) - x| ≤ A := by
  have hdenpos : 0 < 1 + A := by linarith
  have hden : 1 + A ≠ 0 := ne_of_gt hdenpos
  rw [normalized_mixture_difference A x y hden]
  rw [abs_div, abs_mul, abs_of_nonneg hA, abs_of_pos hdenpos]
  have hnum : A * |y - x| ≤ A := by
    nlinarith [abs_nonneg (y - x)]
  have hdiv : A * |y - x| / (1 + A) ≤ A / (1 + A) :=
    (div_le_div_iff_of_pos_right hdenpos).2 hnum
  have hfrac : A / (1 + A) ≤ A := by
    apply (div_le_iff₀ hdenpos).2
    nlinarith
  exact hdiv.trans hfrac

#print axioms transported_exponential_log_rate
#print axioms normalized_mixture_difference
#print axioms normalized_mixture_difference_bound

end YMCallanSymanzikFinite
end MillenniumBraid
