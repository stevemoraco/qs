import Mathlib

namespace PNP
namespace C484PaddingExponentFinite

theorem exponent_conservation
    {a b c r p M : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 < b)
    (hc : 0 ≤ c)
    (_hr : 0 ≤ r)
    (hp : 0 < p)
    (hsim : (b * r + c) / p ≤ M) :
    a * r / p ≤ (a / b) * M := by
  have hbr : b * r ≤ b * r + c := by linarith
  have hdiv : b * r / p ≤ (b * r + c) / p := by
    exact div_le_div_of_nonneg_right hbr (le_of_lt hp)
  have hcore : b * r / p ≤ M := hdiv.trans hsim
  have hab : 0 ≤ a / b := div_nonneg ha (le_of_lt hb)
  have hscaled := mul_le_mul_of_nonneg_left hcore hab
  calc
    a * r / p = (a / b) * (b * r / p) := by
      field_simp [ne_of_gt hb, ne_of_gt hp]
    _ ≤ (a / b) * M := hscaled

theorem hard_excess_forces_simulation_excess
    {a b c r p M : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 < b)
    (hc : 0 ≤ c)
    (hr : 0 ≤ r)
    (hp : 0 < p)
    (hhard : (a / b) * M < a * r / p) :
    M < (b * r + c) / p := by
  by_contra hnot
  have hsim : (b * r + c) / p ≤ M := le_of_not_gt hnot
  have hbound := exponent_conservation ha hb hc hr hp hsim
  exact (not_lt_of_ge hbound) hhard

theorem common_padding_denominator (b r p : ℝ) :
    b * r / p = b * (r / p) := by ring

theorem linear_padding_fixed {r : ℝ} (hr : r ≠ 0) :
    r / r = 1 := by exact div_self hr

theorem quadratic_padding_sublinear {r : ℝ} (hr : r ≠ 0) :
    r / r ^ 2 = 1 / r := by field_simp

#print axioms exponent_conservation
#print axioms hard_excess_forces_simulation_excess
#print axioms common_padding_denominator
#print axioms linear_padding_fixed
#print axioms quadratic_padding_sublinear

end C484PaddingExponentFinite
end PNP
