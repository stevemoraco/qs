import Mathlib

namespace NSNineDirectionStressAlgebra

/-- If `r` strictly dominates `|x|`, both pair weights are positive. -/
theorem pair_weights_positive {r x : ℝ} (h : |x| < r) :
    0 < r + x ∧ 0 < r - x := by
  constructor
  · have hx : -r < x := by
      have := (abs_lt.mp h).1
      linarith
    linarith
  · have hx : x < r := (abs_lt.mp h).2
    linarith

/-- The difference of the two positive pair weights reproduces the desired
off-diagonal coefficient after the normalized rank-one factor `1/2`. -/
theorem pair_offdiag_identity (r x : ℝ) :
    ((r + x) - (r - x)) / 2 = x := by
  ring

/-- The sum of the two pair weights gives exactly the diagonal load `r`. -/
theorem pair_diagonal_identity (r x : ℝ) :
    ((r + x) + (r - x)) / 2 = r := by
  ring

/-- A strict pressure-gauge offset makes the first residual diagonal weight positive. -/
theorem diagonal_weight_one_positive
    {λ s11 r12 r13 : ℝ}
    (h : -s11 + r12 + r13 < λ) :
    0 < λ + s11 - r12 - r13 := by
  linarith

/-- The analogous second residual diagonal weight is positive. -/
theorem diagonal_weight_two_positive
    {λ s22 r12 r23 : ℝ}
    (h : -s22 + r12 + r23 < λ) :
    0 < λ + s22 - r12 - r23 := by
  linarith

/-- The analogous third residual diagonal weight is positive. -/
theorem diagonal_weight_three_positive
    {λ s33 r13 r23 : ℝ}
    (h : -s33 + r13 + r23 < λ) :
    0 < λ + s33 - r13 - r23 := by
  linarith

/-- Entrywise reconstruction of the first diagonal component after adding
its two pair loads and its residual axis weight. -/
theorem diagonal_one_reconstruct (λ s11 r12 r13 : ℝ) :
    (λ + s11 - r12 - r13) + r12 + r13 = λ + s11 := by
  ring

theorem diagonal_two_reconstruct (λ s22 r12 r23 : ℝ) :
    (λ + s22 - r12 - r23) + r12 + r23 = λ + s22 := by
  ring

theorem diagonal_three_reconstruct (λ s33 r13 r23 : ℝ) :
    (λ + s33 - r13 - r23) + r13 + r23 = λ + s33 := by
  ring

#print axioms pair_weights_positive
#print axioms pair_offdiag_identity
#print axioms pair_diagonal_identity
#print axioms diagonal_weight_one_positive
#print axioms diagonal_weight_two_positive
#print axioms diagonal_weight_three_positive
#print axioms diagonal_one_reconstruct
#print axioms diagonal_two_reconstruct
#print axioms diagonal_three_reconstruct

end NSNineDirectionStressAlgebra
