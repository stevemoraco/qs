import Mathlib

open scoped BigOperators

namespace Millennium.YangMills

/-!
# Standalone factorial-Cauchy common-radius certificate

Finite real/infinite-series algebra only. No Yang--Mills or Clay theorem.
-/

/-- An ordinary normalized Cauchy coefficient bound is summable at every
strictly smaller nonnegative radius. -/
theorem cauchy_coefficients_summable_at_smaller_radius_standalone
    (a : ℕ → ℝ)
    (C r rho : ℝ)
    (hr : 0 ≤ r)
    (hrho : 0 < rho)
    (hrrho : r < rho)
    (ha : ∀ k : ℕ, |a k| ≤ C / rho ^ k) :
    Summable (fun k : ℕ => |a k| * r ^ k) := by
  have hq0 : 0 ≤ r / rho := div_nonneg hr hrho.le
  have hqnorm : ‖r / rho‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact (div_lt_one hrho).2 hrrho
  have hgeom : Summable (fun k : ℕ => (r / rho) ^ k) :=
    summable_geometric_of_norm_lt_one hqnorm
  have hmajor : Summable (fun k : ℕ => C * (r / rho) ^ k) :=
    hgeom.mul_left C
  have hnonneg : ∀ k : ℕ, 0 ≤ |a k| * r ^ k := by
    intro k
    exact mul_nonneg (abs_nonneg _) (pow_nonneg hr k)
  have hdom : ∀ k : ℕ, |a k| * r ^ k ≤ C * (r / rho) ^ k := by
    intro k
    have hmul := mul_le_mul_of_nonneg_right (ha k) (pow_nonneg hr k)
    calc
      |a k| * r ^ k ≤ (C / rho ^ k) * r ^ k := hmul
      _ = C * (r / rho) ^ k := by
        rw [div_pow]
        ring
  exact .of_nonneg_of_le hnonneg hdom hmajor

/-- Dividing a factorial Cauchy derivative estimate by the factorial gives the
ordinary normalized coefficient estimate with the same tube radius. -/
theorem normalized_factorial_cauchy_bound_standalone
    (d : ℕ → ℝ)
    (C rho : ℝ)
    (hd : ∀ q : ℕ,
      |d q| ≤ C * (q.factorial : ℝ) / rho ^ q) :
    ∀ q : ℕ,
      |d q / (q.factorial : ℝ)| ≤ C / rho ^ q := by
  intro q
  have hfac : 0 < (q.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos q
  rw [abs_div, abs_of_pos hfac]
  apply (div_le_iff₀ hfac).2
  calc
    |d q| ≤ C * (q.factorial : ℝ) / rho ^ q := hd q
    _ = (C / rho ^ q) * (q.factorial : ℝ) := by ring

/-- The normalized factorial-Cauchy coefficients have a concrete common
positive radius, namely `rho/2`. -/
theorem factorial_cauchy_coefficients_have_common_positive_radius_standalone
    (d : ℕ → ℝ)
    (C rho : ℝ)
    (hrho : 0 < rho)
    (hd : ∀ q : ℕ,
      |d q| ≤ C * (q.factorial : ℝ) / rho ^ q) :
    ∃ r : ℝ,
      0 < r ∧ r < rho ∧
      Summable (fun q : ℕ =>
        |d q / (q.factorial : ℝ)| * r ^ q) := by
  refine ⟨rho / 2, by linarith, by linarith, ?_⟩
  exact cauchy_coefficients_summable_at_smaller_radius_standalone
    (fun q : ℕ => d q / (q.factorial : ℝ)) C (rho / 2) rho
    (by linarith) hrho (by linarith)
    (normalized_factorial_cauchy_bound_standalone d C rho hd)

/-- A uniformly factorial-Cauchy family shares the same half-radius. -/
theorem uniform_factorial_cauchy_family_has_common_positive_radius_standalone
    {ι : Type*}
    (d : ι → ℕ → ℝ)
    (C rho : ℝ)
    (hrho : 0 < rho)
    (hd : ∀ i : ι, ∀ q : ℕ,
      |d i q| ≤ C * (q.factorial : ℝ) / rho ^ q) :
    ∃ r : ℝ,
      0 < r ∧ r < rho ∧
      ∀ i : ι,
        Summable (fun q : ℕ =>
          |d i q / (q.factorial : ℝ)| * r ^ q) := by
  refine ⟨rho / 2, by linarith, by linarith, ?_⟩
  intro i
  exact cauchy_coefficients_summable_at_smaller_radius_standalone
    (fun q : ℕ => d i q / (q.factorial : ℝ)) C (rho / 2) rho
    (by linarith) hrho (by linarith)
    (normalized_factorial_cauchy_bound_standalone (d i) C rho (hd i))

#print axioms cauchy_coefficients_summable_at_smaller_radius_standalone
#print axioms normalized_factorial_cauchy_bound_standalone
#print axioms factorial_cauchy_coefficients_have_common_positive_radius_standalone
#print axioms uniform_factorial_cauchy_family_has_common_positive_radius_standalone

end Millennium.YangMills
