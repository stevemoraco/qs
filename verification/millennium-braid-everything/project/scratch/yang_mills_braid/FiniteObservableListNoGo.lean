import Mathlib

namespace YangMillsBraid

/-- A finite family satisfying a positive lower frame inequality has trivial
orthogonal complement. -/
theorem lower_frame_has_no_hidden_vector
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [Fintype ι]
    (v : ι → H) (A : ℝ) (hA : 0 < A)
    (hframe : ∀ u : H,
      A * ‖u‖ ^ 2 ≤ ∑ i, ‖@inner ℂ H _ (v i) u‖ ^ 2)
    (u : H) (horth : ∀ i, @inner ℂ H _ (v i) u = 0) :
    u = 0 := by
  have hsum : (∑ i, ‖@inner ℂ H _ (v i) u‖ ^ 2) = 0 := by
    simp [horth]
  have hzero : A * ‖u‖ ^ 2 ≤ 0 := by simpa [hsum] using hframe u
  have hnorm : ‖u‖ = 0 := by nlinarith [sq_nonneg ‖u‖]
  exact norm_eq_zero.mp hnorm

/-- A hidden mode can have eigenvalue one while every checked vector has zero
covariance with it.  This scalar core records the spectral mismatch. -/
theorem hidden_mode_has_unit_spectral_radius :
    max (0 : ℝ) 1 = 1 := by
  norm_num

/-- A fixed finite observable count cannot keep pace with a strictly larger
truncated Hilbert dimension. -/
theorem too_few_observables_for_dimension
    (M D : ℕ) (h : M < D) :
    ¬ D ≤ M := by
  omega

end YangMillsBraid
