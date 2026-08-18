import Mathlib

/-!
# Faizal--Shabir weak-RG parabolic cone firewall

Finite real-algebra facts behind the hostile audit of arXiv:2606.19362v1,
Theorem 10.4 / Eqs. (10.34)--(10.35).

The manuscript bounds

  K' <= theta K + c1 g^2,
  g' = g - beta g^3 + R,
  |R| <= c2 g^5 + c3 g K + c3 K^2,

and then claims that choosing a fixed rectangular polydisc |g| <= eps,
K <= delta sufficiently small yields the cubic decrease

  |g'| <= |g| (1 - beta g^2 / 2)

for every K <= delta.  The finite countermodel below records why a fixed
K-width does not by itself make the K^2 channel small relative to g^3 as
g -> 0.  The natural repaired scale is a parabolic cone K <= A g^2.

This file proves only finite scalar algebra.  It does not formalize the
Faizal--Shabir Banach RG map, Yang--Mills, AF/IR identification, OS
reconstruction, a mass gap, or any Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirParabolicAFConeFirewall

theorem mixed_feedback_is_cubic (c3 A g : ℝ) :
    c3 * g * (A * g ^ 2) = c3 * A * g ^ 3 := by
  ring

theorem square_feedback_is_quartic (c3 A g : ℝ) :
    c3 * (A * g ^ 2) ^ 2 = c3 * A ^ 2 * g ^ 4 := by
  ring

theorem parabolic_margin_necessary
    (beta c1 c3 theta A : ℝ)
    (hc3 : 0 ≤ c3)
    (hone : 0 < 1 - theta)
    (hstable : c1 < (1 - theta) * A)
    (hmarginal : 2 * c3 * A < beta) :
    2 * c1 * c3 < beta * (1 - theta) := by
  have hnonneg : 0 ≤ 2 * c3 := by positivity
  have h1 := mul_le_mul_of_nonneg_right (le_of_lt hstable) hnonneg
  have h2 := mul_lt_mul_of_pos_right hmarginal hone
  calc
    2 * c1 * c3 = c1 * (2 * c3) := by ring
    _ ≤ ((1 - theta) * A) * (2 * c3) := h1
    _ = (2 * c3 * A) * (1 - theta) := by ring
    _ < beta * (1 - theta) := h2

theorem small_rectangle_bound_does_not_force_cubic_contraction :
    let g : ℝ := (1 : ℝ) / 10000
    let K : ℝ := (1 : ℝ) / 100
    let R : ℝ := K ^ 2
    0 < g ∧
      g ≤ (1 : ℝ) / 100 ∧
      0 ≤ K ∧
      K ≤ (1 : ℝ) / 100 ∧
      R ≤ g * K + K ^ 2 ∧
      g * (1 - g ^ 2 / 2) < g - g ^ 3 + R := by
  norm_num

theorem cubic_budget_adds
    (beta a b c g R : ℝ)
    (hg : 0 ≤ g)
    (hR : |R| ≤ a * g ^ 3 + b * g ^ 3 + c * g ^ 3)
    (hcoef : a + b + c ≤ beta / 2) :
    |R| ≤ (beta / 2) * g ^ 3 := by
  have hg3 : 0 ≤ g ^ 3 := by positivity
  nlinarith

#print axioms mixed_feedback_is_cubic
#print axioms square_feedback_is_quartic
#print axioms parabolic_margin_necessary
#print axioms small_rectangle_bound_does_not_force_cubic_contraction
#print axioms cubic_budget_adds

end Millennium.YangMills.FaizalShabirParabolicAFConeFirewall
