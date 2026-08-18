import Mathlib

namespace Millennium.RH.FejerRoundingFiniteCore

theorem scalar_fejer_decomp
    (a y r M : ℝ) :
    a * y = (1 - r / M) * a * y + (r / M) * a * y := by
  ring

theorem scalar_rounding_charge
    (a y r M : ℝ)
    (hM : 0 < M)
    (hr : 0 ≤ r)
    (hy : |y| ≤ 1) :
    |(r / M) * a * y| ≤ (r / M) * |a| := by
  have hrM : 0 ≤ r / M := div_nonneg hr (le_of_lt hM)
  calc
    |(r / M) * a * y| = (r / M) * |a| * |y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hrM]
    _ ≤ (r / M) * |a| * 1 := by
      exact mul_le_mul_of_nonneg_left hy (mul_nonneg hrM (abs_nonneg a))
    _ = (r / M) * |a| := by ring

theorem finite_fejer_decomp
    {ι : Type*}
    (s : Finset ι)
    (a y r : ι → ℝ)
    (M : ℝ) :
    (∑ i in s, a i * y i) =
      (∑ i in s, (1 - r i / M) * a i * y i) +
      ∑ i in s, (r i / M) * a i * y i := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact scalar_fejer_decomp (a i) (y i) (r i) M

#print axioms scalar_fejer_decomp
#print axioms scalar_rounding_charge
#print axioms finite_fejer_decomp

end Millennium.RH.FejerRoundingFiniteCore
