import Mathlib

/-!
# Pineau--Vicol modified Bernoulli axial-vorticity finite firewall

Finite algebra only.  This file does **not** formalize the RSS PDE, differential
operators, integration by parts, Pineau--Vicol, Navier--Stokes regularity, or a
Clay theorem.
-/

namespace NSPVModifiedBernoulliAxial

theorem bernoulli_angular_momentum_cancellation
    (alpha lPi dPi dP lK dK omSq om3 : ℝ)
    (hPi : lPi + omSq = alpha * (dPi - dP))
    (hK : lK - alpha * dK = -dP - 2 * om3) :
    (lPi - alpha * dPi) - alpha * (lK - alpha * dK) + omSq =
      2 * alpha * om3 := by
  have hPi' : lPi + omSq - alpha * dPi = -alpha * dP := by
    nlinarith [hPi]
  calc
    (lPi - alpha * dPi) - alpha * (lK - alpha * dK) + omSq =
        (lPi + omSq - alpha * dPi) - alpha * (lK - alpha * dK) := by ring
    _ = (-alpha * dP) - alpha * (-dP - 2 * om3) := by rw [hPi', hK]
    _ = 2 * alpha * om3 := by ring

theorem shifted_vorticity_square
    (alpha om1 om2 om3 : ℝ) :
    2 * alpha * om3 - (om1^2 + om2^2 + om3^2) =
      alpha^2 - (om1^2 + om2^2 + (om3 - alpha)^2) := by
  ring

theorem modified_source_can_be_positive :
    (0 : ℝ) < 2 * 1 * 1 - (0^2 + 0^2 + 1^2) := by
  norm_num

theorem modified_source_can_be_negative :
    2 * (1 : ℝ) * (-1) - (0^2 + 0^2 + (-1)^2) < 0 := by
  norm_num

theorem no_universal_nonpositive_source :
    ¬ (∀ alpha om1 om2 om3 : ℝ,
      2 * alpha * om3 - (om1^2 + om2^2 + om3^2) ≤ 0) := by
  intro h
  have hh := h 1 0 0 1
  norm_num at hh

theorem no_universal_nonnegative_source :
    ¬ (∀ alpha om1 om2 om3 : ℝ,
      0 ≤ 2 * alpha * om3 - (om1^2 + om2^2 + om3^2)) := by
  intro h
  have hh := h 1 0 0 (-1)
  norm_num at hh

theorem radial_gaussian_rotation_terms_cancel
    (alpha K KR piR energy : ℝ)
    (hMain : energy = alpha * K - piR / 2 + alpha * KR / 2)
    (hK : KR / 2 = -K) :
    energy = -piR / 2 := by
  rw [hMain]
  nlinarith [hK]

#print axioms bernoulli_angular_momentum_cancellation
#print axioms shifted_vorticity_square
#print axioms modified_source_can_be_positive
#print axioms modified_source_can_be_negative
#print axioms no_universal_nonpositive_source
#print axioms no_universal_nonnegative_source
#print axioms radial_gaussian_rotation_terms_cancel

end NSPVModifiedBernoulliAxial
