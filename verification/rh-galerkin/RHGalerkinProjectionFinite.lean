import Mathlib

/-!
# RH localized-Weil Galerkin projection: finite scalar core

This file formalizes the finite real-algebra implication used in the current
Suzuki/localized-Weil lower-certificate lane. It does not formalize the
localized Weil operator, its spectrum, the analytic projection estimates, or RH.
-/

namespace RH
namespace GalerkinProjection

/-- If the reference tail `r` splits orthogonally into the true Ritz error `e`
and the projection displacement `d`, while `d ≤ α r` with `0 ≤ α < 1`, then
`e` controls `r` with the sharp scalar denominator `1 - α²`. -/
theorem tail_from_orthogonal_split
    (alpha r e d : ℝ)
    (halpha0 : 0 ≤ alpha)
    (halpha1 : alpha < 1)
    (hr : 0 ≤ r)
    (he : 0 ≤ e)
    (hd : 0 ≤ d)
    (hdelta : d ≤ alpha * r)
    (hsplit : r ^ 2 = e ^ 2 + d ^ 2) :
    (1 - alpha ^ 2) * r ^ 2 ≤ e ^ 2 := by
  have har : 0 ≤ alpha * r := mul_nonneg halpha0 hr
  have hprod : 0 ≤ (alpha * r - d) * (alpha * r + d) :=
    mul_nonneg (sub_nonneg.mpr hdelta) (add_nonneg har hd)
  have hdelta_sq : d ^ 2 ≤ alpha ^ 2 * r ^ 2 := by
    nlinarith
  nlinarith

/-- Finite combination of the projection-tail inequality with a downstream
`L²` estimate `b ≤ β r + γ d`. This is the exact scalar core needed to turn a
reference-mode tail bound into a true Ritz/Galerkin error bound. -/
theorem galerkin_l2_error_core
    (alpha beta gamma r e d b : ℝ)
    (halpha0 : 0 ≤ alpha)
    (halpha1 : alpha < 1)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma)
    (hr : 0 ≤ r)
    (he : 0 ≤ e)
    (hd : 0 ≤ d)
    (hb : 0 ≤ b)
    (hdelta : d ≤ alpha * r)
    (hsplit : r ^ 2 = e ^ 2 + d ^ 2)
    (hl2 : b ≤ beta * r + gamma * d) :
    (1 - alpha ^ 2) * b ^ 2 ≤
      (beta + gamma * alpha) ^ 2 * e ^ 2 := by
  have har : 0 ≤ alpha * r := mul_nonneg halpha0 hr
  have hgamma_gap : 0 ≤ gamma * (alpha * r - d) :=
    mul_nonneg hgamma (sub_nonneg.mpr hdelta)
  have hlinear : beta * r + gamma * d ≤
      (beta + gamma * alpha) * r := by
    nlinarith
  have hc : 0 ≤ beta + gamma * alpha :=
    add_nonneg hbeta (mul_nonneg hgamma halpha0)
  have hcr : 0 ≤ (beta + gamma * alpha) * r := mul_nonneg hc hr
  have hbcr : b ≤ (beta + gamma * alpha) * r := le_trans hl2 hlinear
  have hsquare_prod :
      0 ≤ ((beta + gamma * alpha) * r - b) *
        ((beta + gamma * alpha) * r + b) :=
    mul_nonneg (sub_nonneg.mpr hbcr) (add_nonneg hcr hb)
  have hb_sq : b ^ 2 ≤ (beta + gamma * alpha) ^ 2 * r ^ 2 := by
    nlinarith
  have hfac_prod : 0 ≤ (1 - alpha) * (1 + alpha) :=
    mul_nonneg (sub_nonneg.mpr (le_of_lt halpha1))
      (add_nonneg (by norm_num) halpha0)
  have hfac : 0 ≤ 1 - alpha ^ 2 := by
    nlinarith
  have htail := tail_from_orthogonal_split
    alpha r e d halpha0 halpha1 hr he hd hdelta hsplit
  calc
    (1 - alpha ^ 2) * b ^ 2
        ≤ (1 - alpha ^ 2) *
            ((beta + gamma * alpha) ^ 2 * r ^ 2) :=
          mul_le_mul_of_nonneg_left hb_sq hfac
    _ = (beta + gamma * alpha) ^ 2 *
          ((1 - alpha ^ 2) * r ^ 2) := by ring
    _ ≤ (beta + gamma * alpha) ^ 2 * e ^ 2 :=
          mul_le_mul_of_nonneg_left htail
            (sq_nonneg (beta + gamma * alpha))

/-- Specialization to `γ = 0`: a pure reference-tail estimate transfers to the
true error with no extra displacement term. -/
theorem pure_tail_transfer
    (alpha beta r e b : ℝ)
    (halpha0 : 0 ≤ alpha)
    (halpha1 : alpha < 1)
    (hbeta : 0 ≤ beta)
    (hr : 0 ≤ r)
    (he : 0 ≤ e)
    (hb : 0 ≤ b)
    (hl2 : b ≤ beta * r)
    (herror : (1 - alpha ^ 2) * r ^ 2 ≤ e ^ 2) :
    (1 - alpha ^ 2) * b ^ 2 ≤ beta ^ 2 * e ^ 2 := by
  have hfac_prod : 0 ≤ (1 - alpha) * (1 + alpha) :=
    mul_nonneg (sub_nonneg.mpr (le_of_lt halpha1))
      (add_nonneg (by norm_num) halpha0)
  have hfac : 0 ≤ 1 - alpha ^ 2 := by
    nlinarith
  have hbr : 0 ≤ beta * r := mul_nonneg hbeta hr
  have hsq_prod : 0 ≤ (beta * r - b) * (beta * r + b) :=
    mul_nonneg (sub_nonneg.mpr hl2) (add_nonneg hbr hb)
  have hb_sq : b ^ 2 ≤ beta ^ 2 * r ^ 2 := by
    nlinarith
  calc
    (1 - alpha ^ 2) * b ^ 2
        ≤ (1 - alpha ^ 2) * (beta ^ 2 * r ^ 2) :=
          mul_le_mul_of_nonneg_left hb_sq hfac
    _ = beta ^ 2 * ((1 - alpha ^ 2) * r ^ 2) := by ring
    _ ≤ beta ^ 2 * e ^ 2 :=
          mul_le_mul_of_nonneg_left herror (sq_nonneg beta)

#print axioms tail_from_orthogonal_split
#print axioms galerkin_l2_error_core
#print axioms pure_tail_transfer

end GalerkinProjection
end RH
