import Mathlib

/-!
# Real equal-shell triad: finite sideband-cancellation core

Finite coordinate algebra for
`research/navier-stokes/NS_REAL_EQUAL_SHELL_TRIAD_EXACT_HIGHHIGH_SIDEBAND_CANCELLATION_2026-08-13.md`.

This file does not formalize Fourier analysis, Leray projection, localization,
Navier--Stokes, or blowup.  In particular, the theorem called
`differenceCoefficient_parallel` proves coordinate parallelism only; the
analytic statement that Leray projection kills a frequency-parallel vector is
external.
-/

namespace NSBraid
namespace RealEqualShellTriad

theorem equalShell (K h : ℝ) :
    K^2 + h^2 = (-K)^2 + h^2 := by
  ring

theorem firstTransverse (K h c : ℝ) :
    h * K + (-K) * h + c * 0 = 0 := by
  ring

theorem secondTransverse (K h c : ℝ) :
    h * (-K) + K * h + (-c) * 0 = 0 := by
  ring

theorem firstCrossDot (K h c : ℝ) :
    h * (-K) + (-K) * h + c * 0 = -2 * K * h := by
  ring

theorem secondCrossDot (K h c : ℝ) :
    h * K + K * h + (-c) * 0 = 2 * K * h := by
  ring

theorem sumCoefficient (K h c : ℝ) :
    ((-2 * K * h) * h + (2 * K * h) * h,
     (-2 * K * h) * K + (2 * K * h) * (-K),
     (-2 * K * h) * (-c) + (2 * K * h) * c)
      = (0, -4 * K^2 * h, 4 * K * h * c) := by
  ext <;> ring

theorem differenceCoefficient (K h c : ℝ) :
    ((2 * K * h) * h + (2 * K * h) * h,
     (2 * K * h) * K + (2 * K * h) * (-K),
     (2 * K * h) * (-c) + (2 * K * h) * c)
      = (4 * K * h^2, 0, 0) := by
  ext <;> ring

theorem differenceCoefficient_parallel (K h : ℝ) :
    (4 * K * h^2, (0 : ℝ), (0 : ℝ)) =
      (2 * h^2 * (2 * K), 2 * h^2 * 0, 2 * h^2 * 0) := by
  ext <;> ring

theorem firstSelfZero (K h c : ℝ)
    (hdot : h * K + (-K) * h + c * 0 = 0) :
    ((h * K + (-K) * h + c * 0) * h,
     (h * K + (-K) * h + c * 0) * (-K),
     (h * K + (-K) * h + c * 0) * c) = (0, 0, 0) := by
  rw [hdot]
  norm_num

theorem secondSelfZero (K h c : ℝ)
    (hdot : h * (-K) + K * h + (-c) * 0 = 0) :
    ((h * (-K) + K * h + (-c) * 0) * h,
     (h * (-K) + K * h + (-c) * 0) * K,
     (h * (-K) + K * h + (-c) * 0) * (-c)) = (0, 0, 0) := by
  rw [hdot]
  norm_num

theorem singleLowCannotKillBothOuter
    (h A B C z1 z2 Z : ℝ)
    (hdiff : A * z2 + B * z1 = 0)
    (hout1 : C * z1 = 2 * h * A * Z)
    (hout2 : C * z2 = 2 * h * B * Z)
    (hh : h ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hZ : Z ≠ 0) :
    False := by
  have hscaled : A * (C * z2) + B * (C * z1) = 0 := by
    calc
      A * (C * z2) + B * (C * z1)
          = C * (A * z2 + B * z1) := by ring
      _ = 0 := by rw [hdiff]; ring
  rw [hout2, hout1] at hscaled
  have hzero : 4 * h * A * B * Z = 0 := by
    nlinarith
  have hne : 4 * h * A * B * Z ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (by norm_num) hh) hA) hB) hZ
  exact hne hzero

theorem localizationSeparationExponent (alpha : ℝ) :
    1 - 2 * (alpha - 1) / 3 = (5 - 2 * alpha) / 3 := by
  ring

theorem localizationSeparationPositive (alpha : ℝ)
    (hα : alpha < 5 / 2) :
    0 < 1 - 2 * (alpha - 1) / 3 := by
  rw [localizationSeparationExponent]
  linarith

#print axioms equalShell
#print axioms firstTransverse
#print axioms secondTransverse
#print axioms firstCrossDot
#print axioms secondCrossDot
#print axioms sumCoefficient
#print axioms differenceCoefficient
#print axioms differenceCoefficient_parallel
#print axioms firstSelfZero
#print axioms secondSelfZero
#print axioms singleLowCannotKillBothOuter
#print axioms localizationSeparationExponent
#print axioms localizationSeparationPositive

end RealEqualShellTriad
end NSBraid
