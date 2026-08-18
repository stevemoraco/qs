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

/-- Positive repaired consumer: once the source-specific analysis has supplied
one cubic remainder budget and enough finite-epsilon stable slack, a parabolic
cone is propagated by one weak-RG step.

The theorem deliberately starts after the analytic work that converts the
Faizal--Shabir remainder estimate to `|R| <= (beta/2) g^3`; that conversion is
the model-specific gate. -/
theorem parabolic_cone_step_from_cubic_budget
    (beta theta A c1 eps g R gnext Knext : ℝ)
    (hbeta : 0 < beta)
    (hA : 0 ≤ A)
    (heps : 0 ≤ eps)
    (hg : 0 < g)
    (hgeps : g ≤ eps)
    (hR : |R| ≤ (beta / 2) * g ^ 3)
    (hgnext : gnext = g - beta * g ^ 3 + R)
    (hKnext : Knext ≤ (theta * A + c1) * g ^ 2)
    (hstable :
      theta * A + c1 ≤ A * (1 - (3 * beta / 2) * eps ^ 2) ^ 2)
    (hpositive : (3 * beta / 2) * eps ^ 2 < 1) :
    0 < gnext ∧
      gnext ≤ g * (1 - (beta / 2) * g ^ 2) ∧
      Knext ≤ A * gnext ^ 2 := by
  have hg0 : 0 ≤ g := le_of_lt hg
  have hgeps_sq : g ^ 2 ≤ eps ^ 2 := by nlinarith
  have hRpm := (abs_le.mp hR)
  have hRlo : -(beta / 2) * g ^ 3 ≤ R := by
    nlinarith [hRpm.1]
  have hRhi : R ≤ (beta / 2) * g ^ 3 := hRpm.2
  have hlower : g * (1 - (3 * beta / 2) * g ^ 2) ≤ gnext := by
    rw [hgnext]
    nlinarith
  have hupper : gnext ≤ g * (1 - (beta / 2) * g ^ 2) := by
    rw [hgnext]
    nlinarith
  have hfactor_pos : 0 < 1 - (3 * beta / 2) * g ^ 2 := by
    nlinarith
  have hgnext_pos : 0 < gnext := lt_of_lt_of_le (mul_pos hg hfactor_pos) hlower
  have heps_factor_nonneg : 0 ≤ 1 - (3 * beta / 2) * eps ^ 2 := by
    nlinarith
  have hfactor_cmp :
      1 - (3 * beta / 2) * eps ^ 2 ≤
        1 - (3 * beta / 2) * g ^ 2 := by
    nlinarith
  have hsquares :
      (1 - (3 * beta / 2) * eps ^ 2) ^ 2 ≤
        (1 - (3 * beta / 2) * g ^ 2) ^ 2 := by
    nlinarith
  have hstable_g :
      theta * A + c1 ≤
        A * (1 - (3 * beta / 2) * g ^ 2) ^ 2 := by
    nlinarith
  have hKbound :
      Knext ≤ A * g ^ 2 * (1 - (3 * beta / 2) * g ^ 2) ^ 2 := by
    nlinarith
  have hlower0 : 0 ≤ g * (1 - (3 * beta / 2) * g ^ 2) := by positivity
  have hsquare_lower :
      (g * (1 - (3 * beta / 2) * g ^ 2)) ^ 2 ≤ gnext ^ 2 := by
    nlinarith
  have hKfinal : Knext ≤ A * gnext ^ 2 := by
    nlinarith
  exact ⟨hgnext_pos, hupper, hKfinal⟩

#print axioms mixed_feedback_is_cubic
#print axioms square_feedback_is_quartic
#print axioms parabolic_margin_necessary
#print axioms small_rectangle_bound_does_not_force_cubic_contraction
#print axioms cubic_budget_adds
#print axioms parabolic_cone_step_from_cubic_budget

end Millennium.YangMills.FaizalShabirParabolicAFConeFirewall
