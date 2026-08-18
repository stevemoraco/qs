import Mathlib

/-!
# Faizal--Shabir sharp positive-beta parabolic cone

Finite real-algebra consumers for the hostile repair of arXiv:2606.19362v1,
Theorem 10.4 / Eqs. (10.34)--(10.42).

On the source-native parabolic cone `K <= A g^2`, the leading mixed marginal
channel costs `c3 A g^3`. To obtain *some* strictly positive cubic decrement,
one only needs `c3 A < beta`; the older half-beta budget `2 c3 A < beta` is a
stronger normalization choice, not the sharp leading compatibility condition.

Combining stable-cone slack `c1 < (1-theta) A` with positive marginal slack
`c3 A < beta` forces the sharp leading inequality

  c1*c3 < beta*(1-theta).

The second theorem verifies the positive one-step consumer for an arbitrary
remainder coefficient `rho < beta`, and records explicitly that the surviving
decrement `beta-rho` is positive. The model-specific analytic work must still
produce that cubic remainder budget and the finite-epsilon stable slack.

This file proves only finite scalar algebra. It does not formalize the
Faizal--Shabir Banach RG map, Yang--Mills, AF/IR identification, OS
reconstruction, a mass gap, or any Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirSharpPositiveBetaCone

theorem sharp_leading_margin_necessary
    (beta c1 c3 theta A : ℝ)
    (hc3 : 0 ≤ c3)
    (hone : 0 < 1 - theta)
    (hstable : c1 < (1 - theta) * A)
    (hmarginal : c3 * A < beta) :
    c1 * c3 < beta * (1 - theta) := by
  have h1 := mul_le_mul_of_nonneg_right (le_of_lt hstable) hc3
  have h2 := mul_lt_mul_of_pos_right hmarginal hone
  calc
    c1 * c3 ≤ ((1 - theta) * A) * c3 := h1
    _ = (c3 * A) * (1 - theta) := by ring
    _ < beta * (1 - theta) := h2

theorem parabolic_cone_step_from_positive_beta_budget
    (beta rho theta A c1 eps g R gnext Knext : ℝ)
    (hbeta : 0 < beta)
    (hrho : 0 ≤ rho)
    (hrhobeta : rho < beta)
    (hA : 0 ≤ A)
    (heps : 0 ≤ eps)
    (hg : 0 < g)
    (hgeps : g ≤ eps)
    (hR : |R| ≤ rho * g ^ 3)
    (hgnext : gnext = g - beta * g ^ 3 + R)
    (hKnext : Knext ≤ (theta * A + c1) * g ^ 2)
    (hstable :
      theta * A + c1 ≤ A * (1 - (beta + rho) * eps ^ 2) ^ 2)
    (hpositive : (beta + rho) * eps ^ 2 < 1) :
    0 < beta - rho ∧
      0 < gnext ∧
      gnext ≤ g * (1 - (beta - rho) * g ^ 2) ∧
      Knext ≤ A * gnext ^ 2 := by
  have hdecay : 0 < beta - rho := sub_pos.mpr hrhobeta
  have hRpm := abs_le.mp hR
  have hlower : g * (1 - (beta + rho) * g ^ 2) ≤ gnext := by
    rw [hgnext]
    nlinarith [hRpm.1]
  have hupper : gnext ≤ g * (1 - (beta - rho) * g ^ 2) := by
    rw [hgnext]
    nlinarith [hRpm.2]
  have hfactor_pos : 0 < 1 - (beta + rho) * g ^ 2 := by
    have hgeps_sq : g ^ 2 ≤ eps ^ 2 := by nlinarith
    nlinarith
  have hgnext_pos : 0 < gnext :=
    lt_of_lt_of_le (mul_pos hg hfactor_pos) hlower
  have heps_factor_nonneg : 0 ≤ 1 - (beta + rho) * eps ^ 2 := by
    nlinarith
  have hfactor_cmp :
      1 - (beta + rho) * eps ^ 2 ≤
        1 - (beta + rho) * g ^ 2 := by
    have hgeps_sq : g ^ 2 ≤ eps ^ 2 := by nlinarith
    have hbrho : 0 ≤ beta + rho := by nlinarith
    nlinarith
  have hsquares :
      (1 - (beta + rho) * eps ^ 2) ^ 2 ≤
        (1 - (beta + rho) * g ^ 2) ^ 2 := by
    nlinarith
  have hstable_g :
      theta * A + c1 ≤
        A * (1 - (beta + rho) * g ^ 2) ^ 2 :=
    hstable.trans (mul_le_mul_of_nonneg_left hsquares hA)
  have hmul := mul_le_mul_of_nonneg_right hstable_g (sq_nonneg g)
  have hKbound :
      Knext ≤ A * g ^ 2 * (1 - (beta + rho) * g ^ 2) ^ 2 := by
    calc
      Knext ≤ (theta * A + c1) * g ^ 2 := hKnext
      _ ≤ (A * (1 - (beta + rho) * g ^ 2) ^ 2) * g ^ 2 := hmul
      _ = A * g ^ 2 * (1 - (beta + rho) * g ^ 2) ^ 2 := by ring
  have hlower0 : 0 ≤ g * (1 - (beta + rho) * g ^ 2) := by positivity
  have hsquare_lower :
      (g * (1 - (beta + rho) * g ^ 2)) ^ 2 ≤ gnext ^ 2 := by
    nlinarith
  have hscaled_square := mul_le_mul_of_nonneg_left hsquare_lower hA
  have hKfinal : Knext ≤ A * gnext ^ 2 := by
    calc
      Knext ≤ A * g ^ 2 * (1 - (beta + rho) * g ^ 2) ^ 2 := hKbound
      _ = A * (g * (1 - (beta + rho) * g ^ 2)) ^ 2 := by ring
      _ ≤ A * gnext ^ 2 := hscaled_square
  exact ⟨hdecay, hgnext_pos, hupper, hKfinal⟩

#print axioms sharp_leading_margin_necessary
#print axioms parabolic_cone_step_from_positive_beta_budget

end Millennium.YangMills.FaizalShabirSharpPositiveBetaCone
