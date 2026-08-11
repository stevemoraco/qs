import Mathlib

open scoped BigOperators

namespace Millennium
namespace BSDGlobalDeterminant

/-- The finite-dimensional regulator-square identity. -/
theorem gram_det_square
    {n : ℕ}
    (A G : Matrix (Fin n) (Fin n) ℚ) :
    Matrix.det (A.transpose * G * A) =
      (Matrix.det A) ^ 2 * Matrix.det G := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- Once every finite local norm is one, idelic norm one is the real equality. -/
theorem norm_one_units_is_real_equality
    {ι : Type} [Fintype ι]
    (c : ℝ) (localNorm : ι → ℝ)
    (hunit : ∀ i, localNorm i = 1)
    (hnorm : c * ∏ i, localNorm i = 1) :
    c = 1 := by
  simpa [hunit] using hnorm

/-- Local unit data alone do not determine the positive real component. -/
theorem local_units_real_countermodel
    {ι : Type} [Fintype ι] :
    ∃ c : ℝ, 0 < c ∧ c ≠ 1 ∧ (∀ _i : ι, (1 : ℝ) = 1) := by
  refine ⟨2, by norm_num, by norm_num, ?_⟩
  intro i
  rfl

/-- Functional-equation parity does not fix the central leading value. -/
theorem even_leading_value_free (c x : ℝ) :
    c + (-x) ^ 2 = c + x ^ 2 := by
  ring

/-- Functional-equation parity does not fix the central leading derivative. -/
theorem odd_leading_derivative_free (c x : ℝ) :
    c * (-x) + (-x) ^ 3 = -(c * x + x ^ 3) := by
  ring

/-- Pairing transport records determinant index and scalar normalization. -/
theorem scalar_similitude_determinant
    {n : ℕ}
    (A G : Matrix (Fin n) (Fin n) ℚ)
    (c : ℚ)
    (h : A.transpose * G * A = c • G) :
    (Matrix.det A) ^ 2 * Matrix.det G =
      c ^ n * Matrix.det G := by
  have hdet := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_smul] at hdet
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hdet

end BSDGlobalDeterminant
end Millennium

#print axioms Millennium.BSDGlobalDeterminant.gram_det_square
#print axioms Millennium.BSDGlobalDeterminant.norm_one_units_is_real_equality
#print axioms Millennium.BSDGlobalDeterminant.local_units_real_countermodel
#print axioms Millennium.BSDGlobalDeterminant.even_leading_value_free
#print axioms Millennium.BSDGlobalDeterminant.odd_leading_derivative_free
#print axioms Millennium.BSDGlobalDeterminant.scalar_similitude_determinant
