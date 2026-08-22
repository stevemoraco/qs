import Mathlib

namespace YMScaleCore

theorem quotient_exceeds_target
    {a μ M : ℝ}
    (ha : 0 < a)
    (hscale : M * a < μ) :
    M < μ / a := by
  exact (lt_div_iff₀ ha).2 hscale

theorem linear_rate_quotient
    {a μ m : ℝ}
    (ha : a ≠ 0)
    (hrel : μ = m * a) :
    μ / a = m := by
  rw [hrel]
  field_simp

theorem exists_small_scale
    {μ M : ℝ}
    (hμ : 0 < μ)
    (hM : 0 < M) :
    ∃ a : ℝ, 0 < a ∧ M < μ / a := by
  refine ⟨μ / (2 * M), ?_, ?_⟩
  · positivity
  · have ha : 0 < μ / (2 * M) := by positivity
    apply (lt_div_iff₀ ha).2
    field_simp
    nlinarith

#print axioms quotient_exceeds_target
#print axioms linear_rate_quotient
#print axioms exists_small_scale

end YMScaleCore
