import Mathlib

/-!
# Pineau--Vicol modified Bernoulli axial-vorticity finite firewall

Finite algebra only.  This file does **not** formalize the RSS PDE, differential
operators, integration by parts, Pineau--Vicol, Navier--Stokes regularity, or a
Clay theorem.

It checks the exact algebraic cancellation used in the human derivation:

* the Pineau--Vicol Bernoulli error identity;
* the angular-momentum identity;
* their combination, which leaves only an axial-vorticity source;
* the shifted-vorticity square form;
* explicit sign countermodels showing the new scalar still has no pointwise
  maximum-principle sign;
* the finite algebra behind the hostile radial-Gaussian cancellation, where the
  rotation terms cancel rather than create new coercivity.
-/

namespace NSPVModifiedBernoulliAxial

/-- Abstract algebraic core of
`L_alpha (Pi - alpha K) + |Omega|^2 = 2 alpha Omega_3`.

`lPi,dPi,dP` stand for `L Pi`, `partial_theta Pi`, `partial_theta P`;
`lK,dK` stand for `L K`, `partial_theta K`.
-/
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

/-- The modified source is exactly a shifted-vorticity square defect. -/
theorem shifted_vorticity_square
    (alpha om1 om2 om3 : ℝ) :
    2 * alpha * om3 - (om1^2 + om2^2 + om3^2) =
      alpha^2 - (om1^2 + om2^2 + (om3 - alpha)^2) := by
  ring

/-- The modified Bernoulli source can be strictly positive. -/
theorem modified_source_can_be_positive :
    (0 : ℝ) < 2 * 1 * 1 - (0^2 + 0^2 + 1^2) := by
  norm_num

/-- The same source can also be strictly negative. -/
theorem modified_source_can_be_negative :
    2 * (1 : ℝ) * (-1) - (0^2 + 0^2 + (-1)^2) < 0 := by
  norm_num

/-- Hence no universal nonpositive sign is available from the algebra alone. -/
theorem no_universal_nonpositive_source :
    ¬ (∀ alpha om1 om2 om3 : ℝ,
      2 * alpha * om3 - (om1^2 + om2^2 + om3^2) ≤ 0) := by
  intro h
  have hh := h 1 0 0 1
  norm_num at hh

/-- Nor is the source universally nonnegative. -/
theorem no_universal_nonnegative_source :
    ¬ (∀ alpha om1 om2 om3 : ℝ,
      0 ≤ 2 * alpha * om3 - (om1^2 + om2^2 + om3^2)) := by
  intro h
  have hh := h 1 0 0 (-1)
  norm_num at hh

/-- Finite algebra behind the radial-Gaussian hostile audit.

If a radial pairing gives a main identity with two rotation terms and the
angular-momentum equation gives `KR/2 = -K`, then those rotation terms cancel
exactly; no extra coercive sign is created by that pairing alone.
-/
theorem radial_gaussian_rotation_terms_cancel
    (alpha K KR piR energy : ℝ)
    (hMain : energy = alpha * K - piR / 2 + alpha * KR / 2)
    (hK : KR / 2 = -K) :
    energy = -piR / 2 := by
  calc
    energy = alpha * K - piR / 2 + alpha * KR / 2 := hMain
    _ = alpha * K - piR / 2 + alpha * (KR / 2) := by ring
    _ = alpha * K - piR / 2 + alpha * (-K) := by rw [hK]
    _ = -piR / 2 := by ring

#print axioms bernoulli_angular_momentum_cancellation
#print axioms shifted_vorticity_square
#print axioms modified_source_can_be_positive
#print axioms modified_source_can_be_negative
#print axioms no_universal_nonpositive_source
#print axioms no_universal_nonnegative_source
#print axioms radial_gaussian_rotation_terms_cancel

end NSPVModifiedBernoulliAxial
