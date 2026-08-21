import Mathlib

namespace YM
namespace C483CompressionResidualFinite

def fullGramQ (rho x y : ℝ) : ℝ :=
  x ^ 2 + 2 * rho * x * y + y ^ 2

def mixedMaskQ (rho x y : ℝ) : ℝ :=
  2 * rho * x * y

def compressionResidualQ (rho x y : ℝ) : ℝ :=
  2 * rho * x * y + y ^ 2

def retainedKernelQ (x y : ℝ) : ℝ := x ^ 2

def hiddenCorrectionQ (x y : ℝ) : ℝ := y ^ 2

theorem fullGramQ_half_nonneg (x y : ℝ) :
    0 ≤ fullGramQ (1 / 2) x y := by
  unfold fullGramQ
  nlinarith [sq_nonneg (x + y / 2), sq_nonneg y]

theorem mixedMaskQ_half_negative :
    mixedMaskQ (1 / 2) 1 (-1) < 0 := by
  norm_num [mixedMaskQ]

theorem compressionResidualQ_half_negative :
    compressionResidualQ (1 / 2) (-2) 1 < 0 := by
  norm_num [compressionResidualQ]

theorem zeroCorner_crossBlock_not_nonneg
    {b d : ℝ} (hb : b ≠ 0) :
    ¬ (∀ x y : ℝ, 0 ≤ 2 * b * x * y + d * y ^ 2) := by
  intro h
  let x : ℝ := -(d + 1) / (2 * b)
  have hx : (2 * b) * x = -(d + 1) := by
    dsimp [x]
    field_simp
  have hh := h x 1
  norm_num at hh
  nlinarith

theorem primalFrame_quartic_scaling (t c : ℝ) :
    (t ^ 2 * c) * t ^ 2 = t ^ 4 * c := by ring

theorem hiddenKernel_breaks_relative_bound (eta : ℝ) :
    hiddenCorrectionQ 0 1 > eta * retainedKernelQ 0 1 := by
  norm_num [hiddenCorrectionQ, retainedKernelQ]

theorem hiddenTransfer_above_observed
    {epsilon : ℝ} (_heps : 0 < epsilon) (hhalf : epsilon < 1 / 2) :
    (1 / 2 : ℝ) < 1 - epsilon := by linarith

theorem inverse_stable_derivative_expands
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    1 < q⁻¹ := by
  exact (one_lt_inv₀ hq0).2 hq1

#print axioms fullGramQ_half_nonneg
#print axioms mixedMaskQ_half_negative
#print axioms compressionResidualQ_half_negative
#print axioms zeroCorner_crossBlock_not_nonneg
#print axioms hiddenKernel_breaks_relative_bound
#print axioms inverse_stable_derivative_expands

end C483CompressionResidualFinite
end YM
