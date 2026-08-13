import Mathlib

namespace RHMobiusHyperbolaKernel

noncomputable def bernoulli3 (t : ℝ) : ℝ :=
  t ^ 3 - (3 / 2 : ℝ) * t ^ 2 + (1 / 2 : ℝ) * t

theorem bernoulli3_factor (t : ℝ) :
    bernoulli3 t = t * (t - (1 / 2 : ℝ)) * (t - 1) := by
  unfold bernoulli3
  ring

theorem finiteKernelSum (N : ℕ) (y : ℝ) (hy : y ≠ 0) :
    (Finset.range N).sum
        (fun m => (1 - (((m + 1 : ℕ) : ℝ) / y)) ^ 2) =
      (N : ℝ) - (N : ℝ) * ((N : ℝ) + 1) / y
        + (N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) /
          (6 * y ^ 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp [hy]
      ring

theorem floorKernel_to_bernoulli
    {y n t : ℝ} (hy : y ≠ 0) (hyt : y = n + t) :
    n - n * (n + 1) / y
        + n * (n + 1) * (2 * n + 1) / (6 * y ^ 2) =
      y / 3 - 1 / 2 + 1 / (6 * y)
        - bernoulli3 t / (3 * y ^ 2) := by
  subst y
  unfold bernoulli3
  field_simp [hy]
  ring

#print axioms bernoulli3_factor
#print axioms finiteKernelSum
#print axioms floorKernel_to_bernoulli

end RHMobiusHyperbolaKernel
