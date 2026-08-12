import Mathlib

/-!
# RH logarithmic-window criterion: finite constant arithmetic

Honesty status: this file protects only the elementary real-algebra choices
behind the strip/rate constants. `P` abstracts the positive constant `π`.
It does not formalize `Real.cosh`, Paley--Wiener theory, the exponential-tail
Weil space, the triangular localization, zeta, or RH.
-/

namespace MillenniumBraid
namespace RHLogWindowFinite

theorem midpointStrip
    (P c : ℝ)
    (hP : 0 < P)
    (hc : 0 < c)
    (hcP : c < P) :
    let eta := ((1 / 2 : ℝ) + P / (2 * c)) / 2
    (1 / 2 : ℝ) < eta ∧ c * eta < P / 2 := by
  dsimp
  have hratio : (1 : ℝ) < P / c := by
    exact (lt_div_iff₀ hc).2 hcP
  have hcne : c ≠ 0 := ne_of_gt hc
  have hrewrite :
      (((1 / 2 : ℝ) + P / (2 * c)) / 2)
        = (1 / 4 : ℝ) + P / (4 * c) := by
    field_simp [hcne]
    ring
  rw [hrewrite]
  constructor
  · have : (1 / 4 : ℝ) < P / (4 * c) := by
      nlinarith
    nlinarith
  · have hproduct :
        c * ((1 / 4 : ℝ) + P / (4 * c)) = c / 4 + P / 4 := by
      field_simp [hcne]
      ring
    rw [hproduct]
    nlinarith

theorem midpointRate
    (P C : ℝ)
    (hP : 0 < P)
    (hC : (1 / P : ℝ) < C) :
    let c := (P + 1 / C) / 2
    0 < c ∧ c < P ∧ 1 < c * C := by
  dsimp
  have hInvP : 0 < (1 / P : ℝ) := one_div_pos.mpr hP
  have hCpos : 0 < C := lt_trans hInvP hC
  have hPC : (1 : ℝ) < C * P := by
    exact (div_lt_iff₀ hP).1 hC
  have hInvCLtP : (1 / C : ℝ) < P := by
    apply (div_lt_iff₀ hCpos).2
    nlinarith [hPC]
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hmul : ((P + 1 / C) / 2) * C = (P * C + 1) / 2 := by
    field_simp [hCne]
    ring
  constructor
  · have hInvC : 0 < (1 / C : ℝ) := one_div_pos.mpr hCpos
    nlinarith
  constructor
  · nlinarith
  · rw [hmul]
    nlinarith [hPC]

theorem midpointRateSurplus
    (P C : ℝ)
    (hC : C ≠ 0) :
    ((P + 1 / C) / 2) * C - 1 = (P * C - 1) / 2 := by
  field_simp [hC]
  ring

theorem positiveLogSlope
    (c C L : ℝ)
    (hSlope : 1 < c * C)
    (hL : 0 ≤ L) :
    0 ≤ (c * C - 1) * L := by
  positivity

#print axioms midpointStrip
#print axioms midpointRate
#print axioms midpointRateSurplus
#print axioms positiveLogSlope

end RHLogWindowFinite
end MillenniumBraid
