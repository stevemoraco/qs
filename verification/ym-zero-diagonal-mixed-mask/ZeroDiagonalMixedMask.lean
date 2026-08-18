import Mathlib

/-!
# Zero-diagonal mixed-mask firewall

Finite real 2x2 core of the Yang--Mills mixed-Gram audit.
A symmetric quadratic form with zero diagonal and one off-diagonal
coefficient cannot be positive semidefinite unless that coefficient is zero.

This is only the finite matrix obstruction.  It does not formalize any
Yang--Mills construction or prove/disprove the Millennium problem.
-/

namespace Millennium.YangMills.ZeroDiagonalMixedMask

/-- Zero-diagonal symmetric 2x2 quadratic form with off-diagonal coefficient `b`. -/
def qform (b x y : ℝ) : ℝ := 2 * b * x * y

/-- If the zero-diagonal 2x2 form is nonnegative on every vector, the mixed
coefficient must vanish. -/
theorem offdiag_zero_of_psd
    (b : ℝ)
    (h : ∀ x y : ℝ, 0 ≤ qform b x y) :
    b = 0 := by
  have hpos := h 1 1
  have hneg := h 1 (-1)
  simp [qform] at hpos hneg
  linarith

/-- Every nonzero mixed coefficient gives an explicit failure of PSD. -/
theorem nonzero_offdiag_not_psd
    (b : ℝ) (hb : b ≠ 0) :
    ¬ (∀ x y : ℝ, 0 ≤ qform b x y) := by
  intro h
  exact hb (offdiag_zero_of_psd b h)

/-- The rank-one Gram example `[[1,1],[1,1]]` is PSD, while its pure mixed
mask `[[0,1],[1,0]]` is not PSD.  The first assertion is encoded by the
square `(x+y)^2`; the second by `qform 1`. -/
theorem rank_one_gram_vs_mixed_mask :
    (∀ x y : ℝ, 0 ≤ (x + y)^2) ∧
    ¬ (∀ x y : ℝ, 0 ≤ qform 1 x y) := by
  constructor
  · intro x y
    positivity
  · exact nonzero_offdiag_not_psd 1 (by norm_num)

#print axioms offdiag_zero_of_psd
#print axioms nonzero_offdiag_not_psd
#print axioms rank_one_gram_vs_mixed_mask

end Millennium.YangMills.ZeroDiagonalMixedMask
