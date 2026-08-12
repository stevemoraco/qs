import Mathlib

namespace Run16FiniteCores
namespace SuzukiApproximatePythagoras

theorem sharp_identity (p q x y η : ℝ) :
    (p ^ 2 + q ^ 2 + 2 * η * p * q) *
          (x ^ 2 + y ^ 2 - 2 * η * x * y)
      - (1 - η ^ 2) * (p * x + q * y) ^ 2
    = (x * η * p + x * q - y * η * q - y * p) ^ 2 := by
  ring

theorem sharp_generalized_cauchy (p q x y η : ℝ) :
    (1 - η ^ 2) * (p * x + q * y) ^ 2 ≤
      (p ^ 2 + q ^ 2 + 2 * η * p * q) *
        (x ^ 2 + y ^ 2 - 2 * η * x * y) := by
  calc
    (1 - η ^ 2) * (p * x + q * y) ^ 2
        = (p ^ 2 + q ^ 2 + 2 * η * p * q) *
            (x ^ 2 + y ^ 2 - 2 * η * x * y)
          - (x * η * p + x * q - y * η * q - y * p) ^ 2 := by
            ring
    _ ≤ (p ^ 2 + q ^ 2 + 2 * η * p * q) *
          (x ^ 2 + y ^ 2 - 2 * η * x * y) :=
      sub_le_self _ (sq_nonneg _)

theorem sharp_lower_bound
    (p q x y η L : ℝ)
    (hη0 : 0 ≤ η)
    (hη1 : η < 1)
    (hlinear : 1 ≤ p * x + q * y)
    (hquadratic : x ^ 2 + y ^ 2 - 2 * η * x * y ≤ L)
    (hdenom : 0 < p ^ 2 + q ^ 2 + 2 * η * p * q) :
    (1 - η ^ 2) / (p ^ 2 + q ^ 2 + 2 * η * p * q) ≤ L := by
  let D : ℝ := p ^ 2 + q ^ 2 + 2 * η * p * q
  have hηle : η ≤ 1 := le_of_lt hη1
  have hηmul : η * η ≤ (1 : ℝ) * 1 :=
    mul_le_mul hηle hηle hη0 zero_le_one
  have hcoef : 0 ≤ 1 - η ^ 2 := by
    exact sub_nonneg.mpr (by simpa [pow_two] using hηmul)
  have hlinear0 : 0 ≤ p * x + q * y :=
    le_trans zero_le_one hlinear
  have hlinear_mul : (1 : ℝ) * 1 ≤
      (p * x + q * y) * (p * x + q * y) :=
    mul_le_mul hlinear hlinear zero_le_one hlinear0
  have hlinear_sq : 1 ≤ (p * x + q * y) ^ 2 := by
    simpa [pow_two] using hlinear_mul
  have hfirst :
      1 - η ^ 2 ≤ (1 - η ^ 2) * (p * x + q * y) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hlinear_sq hcoef
    simpa using h
  have hgc := sharp_generalized_cauchy p q x y η
  have hquad_mul :
      D * (x ^ 2 + y ^ 2 - 2 * η * x * y) ≤ D * L := by
    exact mul_le_mul_of_nonneg_left hquadratic (le_of_lt hdenom)
  have hfinal : 1 - η ^ 2 ≤ D * L := by
    calc
      1 - η ^ 2 ≤ (1 - η ^ 2) * (p * x + q * y) ^ 2 := hfirst
      _ ≤ D * (x ^ 2 + y ^ 2 - 2 * η * x * y) := by
        simpa [D] using hgc
      _ ≤ D * L := hquad_mul
  exact (div_le_iff₀ hdenom).2 (by simpa [D, mul_comm] using hfinal)

end SuzukiApproximatePythagoras
end Run16FiniteCores
