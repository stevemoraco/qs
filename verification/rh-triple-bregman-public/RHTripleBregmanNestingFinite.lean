import Mathlib

/-!
Finite algebra for the triple Bregman downstep nesting theorem.

This file does not define primes, Chebyshev theta, logarithmic integrals,
Bregman divergences, Johnston's analytic criterion, or RH. The geometric and
real-analysis identities are external human hypotheses. The declarations below
certify only the exact ordered-field consequences once those identities and
strict slack comparisons are supplied.
-/

namespace RHTripleBregmanNesting

/-- A strictly positive Bregman slack makes any nonpositive prefix jump force
an energy downstep. -/
theorem prefix_loss_forces_energy_loss
    (dH dF b sF : ℝ)
    (hb : 0 < b)
    (hsF : 0 < sF)
    (hF : dF = b * dH + sF)
    (hdown : dF ≤ 0) :
    dH < 0 := by
  nlinarith

/-- The prefix loss is strictly smaller than its affine Johnston-energy loss. -/
theorem prefix_loss_ceiling
    (dH dF b sF : ℝ)
    (hsF : 0 < sF)
    (hF : dF = b * dH + sF) :
    -dF < b * (-dH) := by
  rw [hF]
  linarith

/-- Matching the affine slopes cancels the common energy term; strict
Bregman-curvature domination then compares the two observable jumps. -/
theorem matched_slack_comparison
    (dH dF dA a b lam sF sA : ℝ)
    (hF : dF = b * dH + sF)
    (hA : dA = a * dH + sA)
    (hmatch : a = lam * b)
    (hslack : sA < lam * sF) :
    dA < lam * dF := by
  rw [hF, hA, hmatch]
  ring_nf at *
  linarith

/-- Under positive matched scale, a nonpositive prefix jump forces both the
Robin-type and Johnston-energy downsteps. -/
theorem nested_downsteps
    (dH dF dA a b lam sF sA : ℝ)
    (hb : 0 < b)
    (hlam : 0 < lam)
    (hsF : 0 < sF)
    (hF : dF = b * dH + sF)
    (hA : dA = a * dH + sA)
    (hmatch : a = lam * b)
    (hslack : sA < lam * sF)
    (hdown : dF ≤ 0) :
    dA < 0 ∧ dH < 0 := by
  have hcompare : dA < lam * dF :=
    matched_slack_comparison dH dF dA a b lam sF sA hF hA hmatch hslack
  have hAneg : dA < 0 := by
    nlinarith
  have hHneg : dH < 0 :=
    prefix_loss_forces_energy_loss dH dF b sF hb hsF hF hdown
  exact ⟨hAneg, hHneg⟩

/-- Exact corrected-entropy bookkeeping for a variable decreasing weight. -/
theorem corrected_entropy_increment
    (hPrev hNew dH dF b bNext sF : ℝ)
    (hH : dH = hNew - hPrev)
    (hF : dF = b * dH + sF) :
    dF - bNext * hNew + b * hPrev =
      sF + (b - bNext) * hNew := by
  rw [hF, hH]
  ring

/-- Positive slack, decreasing weight, and nonnegative current energy make the
corrected entropy increment strictly positive. -/
theorem corrected_entropy_positive
    (hNew b bNext sF : ℝ)
    (hsF : 0 < sF)
    (hweight : bNext < b)
    (henergy : 0 ≤ hNew) :
    0 < sF + (b - bNext) * hNew := by
  nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt hweight)) henergy]

/-- Exact rational endpoint certificate used in the explicit `p ≥ 1097`
curvature bound. -/
theorem explicit_curvature_endpoint_certificate :
    (129696875 : ℚ) / 144825414 < 1 := by
  norm_num

#print axioms prefix_loss_forces_energy_loss
#print axioms prefix_loss_ceiling
#print axioms matched_slack_comparison
#print axioms nested_downsteps
#print axioms corrected_entropy_increment
#print axioms corrected_entropy_positive
#print axioms explicit_curvature_endpoint_certificate

end RHTripleBregmanNesting
