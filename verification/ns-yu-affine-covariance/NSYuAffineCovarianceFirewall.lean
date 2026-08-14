import Mathlib

noncomputable section

/-!
# Navier--Stokes: Yu affine-covariance finite firewall

Finite scalar algebra extracted from the filtered-vorticity low-mode audit of
Runlong Yu, arXiv:2606.27560v1 (25 Jun 2026), stacked on the reservoir and
affine-low-mode audits.

For an actual weighted mean of the filtered vorticity equation, the continuum
identity has the schematic form

  m' - S_aff m = Cov(S, Omega) + (Sbar - S_aff)m + Flux.

This file formalizes only the two-point covariance algebra and the reusable
strict-error-budget inequality.  It does not formalize filtering, integration
by parts, Poincare estimates, affine-jet identification, Navier--Stokes
regularity, or blowup.
-/

namespace NSYuAffineCovarianceFirewall

/-- Equal-weight mean of two scalar samples. -/
def mean2 (x y : ℝ) : ℝ := (x + y) / 2

/-- Equal-weight mean of a scalar product sampled at two points. -/
def productMean2 (s₁ s₂ w₁ w₂ : ℝ) : ℝ :=
  (s₁ * w₁ + s₂ * w₂) / 2

/-- Exact two-point covariance identity.  It isolates the product of the strain
and vorticity fluctuations from their coherent means. -/
theorem twoPoint_covariance_identity
    (s₁ s₂ w₁ w₂ : ℝ) :
    productMean2 s₁ s₂ w₁ w₂ - mean2 s₁ s₂ * mean2 w₁ w₂ =
      ((s₁ - s₂) * (w₁ - w₂)) / 4 := by
  unfold productMean2 mean2
  ring

/-- If the strain sample is spatially coherent, the covariance vanishes. -/
theorem coherentStrain_kills_covariance
    (s w₁ w₂ : ℝ) :
    productMean2 s s w₁ w₂ - mean2 s s * mean2 w₁ w₂ = 0 := by
  rw [twoPoint_covariance_identity]
  ring

/-- If the vorticity sample is spatially coherent, the covariance vanishes. -/
theorem coherentVorticity_kills_covariance
    (s₁ s₂ w : ℝ) :
    productMean2 s₁ s₂ w w - mean2 s₁ s₂ * mean2 w w = 0 := by
  rw [twoPoint_covariance_identity]
  ring

/-- Two-point finite shadow of
`m' - Sbar*m = covariance + flux`. -/
theorem twoPoint_meanMismatch_decomposition
    (mPrime s₁ s₂ w₁ w₂ flux : ℝ)
    (hdyn : mPrime = productMean2 s₁ s₂ w₁ w₂ + flux) :
    mPrime - mean2 s₁ s₂ * mean2 w₁ w₂ =
      ((s₁ - s₂) * (w₁ - w₂)) / 4 + flux := by
  rw [hdyn]
  unfold productMean2 mean2
  ring

/-- Two-point finite shadow of the full affine-jet identity

`m' - S_aff*m = covariance + (Sbar-S_aff)*m + flux`.

The extra term records that a chosen far-field affine jet need not equal the
full weighted mean strain. -/
theorem twoPoint_affineJetMismatch_decomposition
    (mPrime s₁ s₂ w₁ w₂ sAff flux : ℝ)
    (hdyn : mPrime = productMean2 s₁ s₂ w₁ w₂ + flux) :
    mPrime - sAff * mean2 w₁ w₂ =
      ((s₁ - s₂) * (w₁ - w₂)) / 4 +
        (mean2 s₁ s₂ - sAff) * mean2 w₁ w₂ + flux := by
  rw [hdyn]
  unfold productMean2 mean2
  ring

/-- Elementary Young bound on the active two-point covariance. -/
theorem covariance_upper_bound
    (a b : ℝ) :
    a * b / 4 ≤ (a ^ 2 + b ^ 2) / 8 := by
  nlinarith [sq_nonneg (a - b)]

/-- If the two fluctuation squares have budgets `alpha*P` and `beta*P`, then
positive covariance is bounded by `(alpha+beta)P/8`. -/
theorem covariance_upper_of_square_budgets
    (a b alpha beta P : ℝ)
    (ha : a ^ 2 ≤ alpha * P)
    (hb : b ^ 2 ≤ beta * P) :
    a * b / 4 ≤ (alpha + beta) * P / 8 := by
  have hy := covariance_upper_bound a b
  nlinarith

/-- A genuine strict coefficient margin converts square-fluctuation control into
strict absorption.  This is the scalar endpoint needed after PDE estimates have
supplied the two square budgets. -/
theorem covariance_strictly_absorbed
    (a b alpha beta eps P : ℝ)
    (hP : 0 < P)
    (ha : a ^ 2 ≤ alpha * P)
    (hb : b ^ 2 ≤ beta * P)
    (hcoeff : alpha + beta < 8 * eps) :
    a * b / 4 < eps * P := by
  have hcov := covariance_upper_of_square_budgets a b alpha beta P ha hb
  have hmul : (alpha + beta) * P < (8 * eps) * P :=
    mul_lt_mul_of_pos_right hcoeff hP
  nlinarith

/-- Three independently controlled residual classes fit under one strict
endpoint margin once their coefficient sum is strictly smaller than the retained
margin. -/
theorem threeResidualBudgets_strictly_absorb
    (cov jet flux deltaCov deltaJet deltaFlux eps P : ℝ)
    (hP : 0 < P)
    (hcov : cov ≤ deltaCov * P)
    (hjet : jet ≤ deltaJet * P)
    (hflux : flux ≤ deltaFlux * P)
    (hmargin : deltaCov + deltaJet + deltaFlux < eps) :
    cov + jet + flux < eps * P := by
  have hsum :
      cov + jet + flux ≤ (deltaCov + deltaJet + deltaFlux) * P := by
    nlinarith
  have hstrict :
      (deltaCov + deltaJet + deltaFlux) * P < eps * P :=
    mul_lt_mul_of_pos_right hmargin hP
  exact lt_of_le_of_lt hsum hstrict

#print axioms twoPoint_covariance_identity
#print axioms coherentStrain_kills_covariance
#print axioms coherentVorticity_kills_covariance
#print axioms twoPoint_meanMismatch_decomposition
#print axioms twoPoint_affineJetMismatch_decomposition
#print axioms covariance_upper_bound
#print axioms covariance_upper_of_square_budgets
#print axioms covariance_strictly_absorbed
#print axioms threeResidualBudgets_strictly_absorb

end NSYuAffineCovarianceFirewall
