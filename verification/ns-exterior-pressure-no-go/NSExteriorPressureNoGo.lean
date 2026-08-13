import Mathlib

/-!
# Single-relay exterior-pressure no-go

This file formalizes the scalar algebra at the load-bearing point of the
real-polarization equal-shell planar Navier--Stokes relay audit.

The geometric calculation supplies two necessary equations for pressure-killing
the target--pump exterior outputs:

* `E * B = 2 * A * F * v`;
* `E * D = 2 * C * F * v`.

Here `C * B - A * D` is exactly the determinant multiplying the desired
pump--pump sum output.  The theorem proves that simultaneous exterior
cancellation forces this determinant to vanish whenever the target polarization
`(E,F)` is nonzero and `v` is nonzero.

No PDE conclusion is encoded in an assumption or theorem statement.
-/

namespace NSExteriorPressureNoGo

/-- The two exterior normal-component cancellation equations force the
pump determinant to vanish whenever the target polarization is nonzero. -/
theorem exterior_z_cancel_forces_desired_det_zero
    {A B C D E F v : ℝ}
    (hv : v ≠ 0)
    (htarget : E ≠ 0 ∨ F ≠ 0)
    (hp : E * B = 2 * A * F * v)
    (hq : E * D = 2 * C * F * v) :
    C * B - A * D = 0 := by
  by_cases hE : E = 0
  · have hF : F ≠ 0 := by
      rcases htarget with hE' | hF
      · exact (hE' hE).elim
      · exact hF
    have hcoeff : 2 * F * v ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) hF) hv
    have hAprod : (2 * F * v) * A = 0 := by
      calc
        (2 * F * v) * A = 2 * A * F * v := by ring
        _ = E * B := hp.symm
        _ = 0 := by simp [hE]
    have hCprod : (2 * F * v) * C = 0 := by
      calc
        (2 * F * v) * C = 2 * C * F * v := by ring
        _ = E * D := hq.symm
        _ = 0 := by simp [hE]
    have hA : A = 0 := (mul_eq_zero.mp hAprod).resolve_left hcoeff
    have hC : C = 0 := (mul_eq_zero.mp hCprod).resolve_left hcoeff
    rw [hA, hC]
    ring
  · have hmul : E * (C * B - A * D) = 0 := by
      calc
        E * (C * B - A * D) = C * (E * B) - A * (E * D) := by ring
        _ = C * (2 * A * F * v) - A * (2 * C * F * v) := by
          rw [hp, hq]
        _ = 0 := by ring
    exact (mul_eq_zero.mp hmul).resolve_left hE

/-- Contrapositive form: a nonzero desired determinant forces at least one
of the two target--pump exterior normal components to survive. -/
theorem desired_det_nonzero_forces_exterior_leakage
    {A B C D E F v : ℝ}
    (hv : v ≠ 0)
    (htarget : E ≠ 0 ∨ F ≠ 0)
    (hdet : C * B - A * D ≠ 0) :
    E * B - 2 * A * F * v ≠ 0 ∨
      2 * C * F * v - E * D ≠ 0 := by
  by_contra hnone
  push Not at hnone
  apply hdet
  apply exterior_z_cancel_forces_desired_det_zero hv htarget
  · linarith [hnone.1]
  · linarith [hnone.2]

/-- Algebraic identity exposing the determinant as the cross-difference of the
two exterior cancellation equations. -/
theorem determinant_cross_difference
    (A B C D E F v : ℝ) :
    E * (C * B - A * D) =
      C * (E * B - 2 * A * F * v) +
      A * (2 * C * F * v - E * D) := by
  ring

#print axioms exterior_z_cancel_forces_desired_det_zero
#print axioms desired_det_nonzero_forces_exterior_leakage
#print axioms determinant_cross_difference

end NSExteriorPressureNoGo
