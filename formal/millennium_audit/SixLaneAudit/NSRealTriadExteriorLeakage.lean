import Mathlib

/-!
# Navier--Stokes real-triad exterior-leakage audit

Finite polynomial core only. This file does not formalize Fourier analysis,
Leray projection, Navier--Stokes evolution, viscosity, singularity formation,
or any Clay Millennium statement.
-/

namespace SixLaneAudit.NSRealTriadExteriorLeakage

/-- In the equal-shell real-triad reduction, the desired determinant cannot
exceed twice the squared size of the two exterior coordinates. -/
theorem determinant_sq_le_two_horizontal_energy
    (alpha A beta B : Real)
    (hA : A ^ 2 <= 1)
    (hB : B ^ 2 <= 1) :
    (alpha * B - beta * A) ^ 2 <= 2 * (alpha ^ 2 + beta ^ 2) := by
  have ha : 0 <= alpha ^ 2 := sq_nonneg alpha
  have hb : 0 <= beta ^ 2 := sq_nonneg beta
  have haB : 0 <= alpha ^ 2 * (1 - B ^ 2) :=
    mul_nonneg ha (sub_nonneg.mpr hB)
  have hbA : 0 <= beta ^ 2 * (1 - A ^ 2) :=
    mul_nonneg hb (sub_nonneg.mpr hA)
  have hsum : 0 <= (alpha * B + beta * A) ^ 2 :=
    sq_nonneg (alpha * B + beta * A)
  nlinarith [haB, hbA, hsum]

/-- Restoring the common geometric scale preserves the leakage floor. -/
theorem scaled_desired_sq_le_two_exterior_sq
    (lambda alpha A beta B : Real)
    (hA : A ^ 2 <= 1)
    (hB : B ^ 2 <= 1) :
    (lambda * (alpha * B - beta * A)) ^ 2 <=
      2 * ((lambda * alpha) ^ 2 + (lambda * beta) ^ 2) := by
  have hdet := determinant_sq_le_two_horizontal_energy alpha A beta B hA hB
  have hlambda : 0 <= lambda ^ 2 := sq_nonneg lambda
  have hmul :
      0 <= lambda ^ 2 *
        (2 * (alpha ^ 2 + beta ^ 2) - (alpha * B - beta * A) ^ 2) :=
    mul_nonneg hlambda (sub_nonneg.mpr hdet)
  nlinarith [hmul]

/-- Exact determinant identity isolating one target coordinate. -/
theorem exterior_gamma_identity
    (kappa alpha A beta B gamma C : Real) :
    alpha * (2 * beta * kappa * C + gamma * B) -
        beta * (2 * alpha * kappa * C + gamma * A) =
      gamma * (alpha * B - beta * A) := by
  ring

/-- Exact determinant identity isolating the other target coordinate. -/
theorem exterior_C_identity
    (kappa alpha A beta B gamma C : Real) :
    B * (2 * alpha * kappa * C + gamma * A) -
        A * (2 * beta * kappa * C + gamma * B) =
      2 * kappa * C * (alpha * B - beta * A) := by
  ring

/-- An active desired relay, a nondegenerate equal-shell angle, and vanishing
of both target--pump exterior sectors force both target coordinates to vanish.
The pump-conjugate relation is retained to certify a nonzero input coordinate. -/
theorem incompatible_vanishing_sectors
    (kappa alpha A beta B gamma C : Real)
    (hkappa : kappa != 0)
    (hpump : alpha * B + beta * A = 0)
    (hdesired : alpha * B - beta * A != 0)
    (hextP : 2 * alpha * kappa * C + gamma * A = 0)
    (hextQ : 2 * beta * kappa * C + gamma * B = 0) :
    gamma = 0 ∧ C = 0 := by
  have hgammadet : gamma * (alpha * B - beta * A) = 0 := by
    calc
      gamma * (alpha * B - beta * A) =
          alpha * (2 * beta * kappa * C + gamma * B) -
            beta * (2 * alpha * kappa * C + gamma * A) := by ring
      _ = 0 := by rw [hextQ, hextP]; ring
  have hgamma : gamma = 0 :=
    (mul_eq_zero.mp hgammadet).resolve_right hdesired
  have halphaB : alpha * B != 0 := by
    intro hzero
    apply hdesired
    nlinarith [hpump, hzero]
  have halpha : alpha != 0 := by
    intro hzero
    apply halphaB
    simp [hzero]
  have hextP0 : (2 * alpha * kappa) * C = 0 := by
    calc
      (2 * alpha * kappa) * C = 2 * alpha * kappa * C + gamma * A := by
        rw [hgamma]
        ring
      _ = 0 := hextP
  have hcoef : 2 * alpha * kappa != 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) halpha) hkappa
  have hC : C = 0 :=
    (mul_eq_zero.mp hextP0).resolve_left hcoef
  exact ⟨hgamma, hC⟩

#print axioms determinant_sq_le_two_horizontal_energy
#print axioms scaled_desired_sq_le_two_exterior_sq
#print axioms exterior_gamma_identity
#print axioms exterior_C_identity
#print axioms incompatible_vanishing_sectors

end SixLaneAudit.NSRealTriadExteriorLeakage
