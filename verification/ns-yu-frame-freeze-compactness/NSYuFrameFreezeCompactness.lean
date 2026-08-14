import Mathlib

/-!
# Navier–Stokes Yu frame-freeze compactness firewalls

Finite scalar and diagonal symmetric-matrix algebra only.

These declarations do **not** formalize Yu's filtered Navier–Stokes estimates,
prove that an actual exterior harmonic strain has the hypotheses below, construct
a singular profile, or prove Navier–Stokes regularity/blow-up.  They isolate the
finite algebra needed by the accompanying gap-visible affine-frame audit.
-/

namespace NSYuFrameFreezeCompactness

noncomputable section

/-- Rayleigh-quotient frame-stability budget.

Think of `lambda1 >= lambda2 >= lambda3` as the eigenvalues of a reference
symmetric matrix in its eigenbasis and `mu` as the top Rayleigh value of a
perturbed matrix.  If the perturbed top value is at least `lambda1-delta` while
its value at the new maximizing unit vector is at most the old quadratic form
plus `delta`, then the old top eigengap charges transverse mass of the new top
vector by at most `2*delta`.
-/
theorem rayleigh_perturbation_frame_budget
    (lambda1 lambda2 lambda3 y1 y2 y3 mu delta gamma : ℝ)
    (horder : lambda3 ≤ lambda2)
    (hgap : gamma = lambda1 - lambda2)
    (hunit : y1 ^ 2 + y2 ^ 2 + y3 ^ 2 = 1)
    (hlow : lambda1 - delta ≤ mu)
    (hupper :
      mu ≤ lambda1 * y1 ^ 2 + lambda2 * y2 ^ 2 + lambda3 * y3 ^ 2 + delta) :
    gamma * (y2 ^ 2 + y3 ^ 2) ≤ 2 * delta := by
  have hdeficit :
      lambda1 -
          (lambda1 * y1 ^ 2 + lambda2 * y2 ^ 2 + lambda3 * y3 ^ 2)
        ≤ 2 * delta := by
    linarith
  have hid :
      lambda1 -
          (lambda1 * y1 ^ 2 + lambda2 * y2 ^ 2 + lambda3 * y3 ^ 2) =
        (lambda1 - lambda2) * y2 ^ 2 +
          (lambda1 - lambda3) * y3 ^ 2 := by
    linear_combination -lambda1 * hunit
  have h13 : gamma ≤ lambda1 - lambda3 := by
    rw [hgap]
    linarith
  have hmul :
      gamma * y3 ^ 2 ≤ (lambda1 - lambda3) * y3 ^ 2 :=
    mul_le_mul_of_nonneg_right h13 (sq_nonneg y3)
  calc
    gamma * (y2 ^ 2 + y3 ^ 2) =
        gamma * y2 ^ 2 + gamma * y3 ^ 2 := by ring
    _ ≤ gamma * y2 ^ 2 + (lambda1 - lambda3) * y3 ^ 2 :=
      add_le_add (le_refl _) hmul
    _ = (lambda1 - lambda2) * y2 ^ 2 +
          (lambda1 - lambda3) * y3 ^ 2 := by rw [hgap]
    _ = lambda1 -
          (lambda1 * y1 ^ 2 + lambda2 * y2 ^ 2 + lambda3 * y3 ^ 2) :=
      hid.symm
    _ ≤ 2 * delta := hdeficit

/-- Positive eigengap converts the Rayleigh perturbation budget into a squared
transverse-angle bound. -/
theorem rayleigh_perturbation_frame_ratio
    (lambda1 lambda2 lambda3 y1 y2 y3 mu delta gamma : ℝ)
    (horder : lambda3 ≤ lambda2)
    (hgap : gamma = lambda1 - lambda2)
    (hgamma : 0 < gamma)
    (hunit : y1 ^ 2 + y2 ^ 2 + y3 ^ 2 = 1)
    (hlow : lambda1 - delta ≤ mu)
    (hupper :
      mu ≤ lambda1 * y1 ^ 2 + lambda2 * y2 ^ 2 + lambda3 * y3 ^ 2 + delta) :
    y2 ^ 2 + y3 ^ 2 ≤ (2 * delta) / gamma := by
  have hbudget : gamma * (y2 ^ 2 + y3 ^ 2) ≤ 2 * delta :=
    rayleigh_perturbation_frame_budget
      lambda1 lambda2 lambda3 y1 y2 y3 mu delta gamma
      horder hgap hunit hlow hupper
  exact (le_div_iff₀ hgamma).2 (by simpa [mul_comm] using hbudget)

/-- If the perturbation itself is at most an `eta` fraction of the top eigengap,
the new top frame has at most `2*eta` squared transverse mass in the old frame. -/
theorem relative_perturbation_freezes_frame
    (lambda1 lambda2 lambda3 y1 y2 y3 mu delta gamma eta : ℝ)
    (horder : lambda3 ≤ lambda2)
    (hgap : gamma = lambda1 - lambda2)
    (hgamma : 0 < gamma)
    (hunit : y1 ^ 2 + y2 ^ 2 + y3 ^ 2 = 1)
    (hlow : lambda1 - delta ≤ mu)
    (hupper :
      mu ≤ lambda1 * y1 ^ 2 + lambda2 * y2 ^ 2 + lambda3 * y3 ^ 2 + delta)
    (hdelta : delta ≤ eta * gamma) :
    y2 ^ 2 + y3 ^ 2 ≤ 2 * eta := by
  have hbudget : gamma * (y2 ^ 2 + y3 ^ 2) ≤ 2 * delta :=
    rayleigh_perturbation_frame_budget
      lambda1 lambda2 lambda3 y1 y2 y3 mu delta gamma
      horder hgap hunit hlow hupper
  have hdelta2 : 2 * delta ≤ 2 * (eta * gamma) := by
    nlinarith
  have hmul :
      gamma * (y2 ^ 2 + y3 ^ 2) ≤ gamma * (2 * eta) := by
    calc
      gamma * (y2 ^ 2 + y3 ^ 2) ≤ 2 * delta := hbudget
      _ ≤ 2 * (eta * gamma) := hdelta2
      _ = gamma * (2 * eta) := by ring
  exact (mul_le_mul_left hgamma).mp hmul

/-- Abstract shell-comparison interface.  Once harmonic scale separation gives
`scaledVariation <= theta * visibleScale` and spectral visibility gives
`visibleScale <= gamma`, nonnegative `theta` transfers the scale separation to
the eigengap itself. -/
theorem gap_visibility_transfers_scale_separation
    (scaledVariation theta visibleScale gamma : ℝ)
    (htheta : 0 ≤ theta)
    (hscaled : scaledVariation ≤ theta * visibleScale)
    (hvisible : visibleScale ≤ gamma) :
    scaledVariation ≤ theta * gamma := by
  exact hscaled.trans (mul_le_mul_of_nonneg_left hvisible htheta)

/-- Two-stage transverse-error composition.  If a vector is close to a moving
axis in the two transverse coordinates and that moving axis is itself close to
the fixed reference axis, then the total transverse mass is at most twice the
sum of the two budgets. -/
theorem two_step_transverse_budget
    (x2 x3 y2 y3 movingError frameError : ℝ)
    (hmove : (x2 - y2) ^ 2 + (x3 - y3) ^ 2 ≤ movingError)
    (hframe : y2 ^ 2 + y3 ^ 2 ≤ frameError) :
    x2 ^ 2 + x3 ^ 2 ≤ 2 * (movingError + frameError) := by
  have hx2 :
      x2 ^ 2 ≤ 2 * (x2 - y2) ^ 2 + 2 * y2 ^ 2 := by
    nlinarith [sq_nonneg (x2 - 2 * y2)]
  have hx3 :
      x3 ^ 2 ≤ 2 * (x3 - y3) ^ 2 + 2 * y3 ^ 2 := by
    nlinarith [sq_nonneg (x3 - 2 * y3)]
  nlinarith

#print axioms rayleigh_perturbation_frame_budget
#print axioms rayleigh_perturbation_frame_ratio
#print axioms relative_perturbation_freezes_frame
#print axioms gap_visibility_transfers_scale_separation
#print axioms two_step_transverse_budget

end

end NSYuFrameFreezeCompactness
