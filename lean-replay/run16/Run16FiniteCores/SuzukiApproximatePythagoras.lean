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
  have hsquare :
      0 ≤ (x * η * p + x * q - y * η * q - y * p) ^ 2 :=
    sq_nonneg _
  nlinarith [sharp_identity p q x y η]

theorem sharp_lower_bound
    (p q x y η λ : ℝ)
    (hη0 : 0 ≤ η)
    (hη1 : η < 1)
    (hp : 0 ≤ p)
    (hq : 0 ≤ q)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y)
    (hlinear : 1 ≤ p * x + q * y)
    (hquadratic : x ^ 2 + y ^ 2 - 2 * η * x * y ≤ λ)
    (hdenom : 0 < p ^ 2 + q ^ 2 + 2 * η * p * q) :
    (1 - η ^ 2) / (p ^ 2 + q ^ 2 + 2 * η * p * q) ≤ λ := by
  let D : ℝ := p ^ 2 + q ^ 2 + 2 * η * p * q
  have hcoef : 0 ≤ 1 - η ^ 2 := by
    nlinarith
  have hlinear_sq : 1 ≤ (p * x + q * y) ^ 2 := by
    nlinarith
  have hfirst :
      1 - η ^ 2 ≤ (1 - η ^ 2) * (p * x + q * y) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hlinear_sq hcoef
    simpa using h
  have hgc := sharp_generalized_cauchy p q x y η
  have hquad_mul :
      D * (x ^ 2 + y ^ 2 - 2 * η * x * y) ≤ D * λ := by
    exact mul_le_mul_of_nonneg_left hquadratic (le_of_lt hdenom)
  have hfinal : 1 - η ^ 2 ≤ D * λ := by
    calc
      1 - η ^ 2 ≤ (1 - η ^ 2) * (p * x + q * y) ^ 2 := hfirst
      _ ≤ D * (x ^ 2 + y ^ 2 - 2 * η * x * y) := by
        simpa [D] using hgc
      _ ≤ D * λ := hquad_mul
  exact (div_le_iff₀ hdenom).2 (by simpa [D, mul_comm] using hfinal)

end SuzukiApproximatePythagoras
end Run16FiniteCores
