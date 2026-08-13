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

/-- The two symmetric high carriers lie on exactly the same Fourier shell. -/
theorem equalShell (K h : ℝ) :
    K^2 + h^2 = (-K)^2 + h^2 := by
  ring

/-- `a=(h,-K,c)` is transverse to `k1=(K,h,0)`. -/
theorem firstTransverse (K h c : ℝ) :
    h * K + (-K) * h + c * 0 = 0 := by
  ring

/-- `b=(h,K,-c)` is transverse to `k2=(-K,h,0)`. -/
theorem secondTransverse (K h c : ℝ) :
    h * (-K) + K * h + (-c) * 0 = 0 := by
  ring

/-- Exact cross dot product `a · k2 = -2Kh`. -/
theorem firstCrossDot (K h c : ℝ) :
    h * (-K) + (-K) * h + c * 0 = -2 * K * h := by
  ring

/-- Exact cross dot product `b · k1 = 2Kh`. -/
theorem secondCrossDot (K h c : ℝ) :
    h * K + K * h + (-c) * 0 = 2 * K * h := by
  ring

/-- The desired sum-mode unprojected coefficient has the displayed
coordinates.  Since the sum frequency is `(0,2h,0)`, its `z` coordinate
survives the Leray projection. -/
theorem sumCoefficient (K h c : ℝ) :
    ((-2 * K * h) * h + (2 * K * h) * h,
     (-2 * K * h) * K + (2 * K * h) * (-K),
     (-2 * K * h) * (-c) + (2 * K * h) * c)
      = (0, -4 * K^2 * h, 4 * K * h * c) := by
  ext <;> ring

/-- The real-conjugate difference-mode coefficient is exactly parallel to
`d=(2K,0,0)`: its y and z coordinates vanish and its x coordinate is
`4Kh^2`. -/
theorem differenceCoefficient (K h c : ℝ) :
    ((2 * K * h) * h + (2 * K * h) * h,
     (2 * K * h) * K + (2 * K * h) * (-K),
     (2 * K * h) * (-c) + (2 * K * h) * c)
      = (4 * K * h^2, 0, 0) := by
  ext <;> ring

/-- Cleared-denominator parallelism certificate: the difference coefficient
is `2 h^2` times the difference frequency `(2K,0,0)`. -/
theorem differenceCoefficient_parallel (K h : ℝ) :
    (4 * K * h^2, (0 : ℝ), (0 : ℝ)) =
      (2 * h^2 * (2 * K), 2 * h^2 * 0, 2 * h^2 * 0) := by
  ext <;> ring

/-- Self-advection of the first carrier vanishes once transversality is used. -/
theorem firstSelfZero (K h c : ℝ)
    (hdot : h * K + (-K) * h + c * 0 = 0) :
    (hdot * h, hdot * (-K), hdot * c) = (0, 0, 0) := by
  simp [hdot]

/-- Self-advection of the second carrier vanishes once transversality is used. -/
theorem secondSelfZero (K h c : ℝ)
    (hdot : h * (-K) + K * h + (-c) * 0 = 0) :
    (hdot * h, hdot * K, hdot * (-c)) = (0, 0, 0) := by
  simp [hdot]

/-- Algebraic no-go for trying to finish the symmetric real triad with only
one low polarization.  Write the two high polarizations in the general form
`a=(h*A,-K*A,z1)` and `b=(h*B,K*B,z2)`, and a low polarization as
`p=(C,0,Z)`.

The first hypothesis is exactly the z-coordinate condition required for the
high-high difference sideband to be frequency-parallel.  The next two are
necessary z-coordinate conditions for *both* low-high outer sidebands to be
frequency-parallel.  If the vertical carrier, both in-plane high components,
and the low z-component are nonzero, these three conditions are incompatible.
-/
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

/-- The localization-scale exponent used by the parent packet construction. -/
theorem localizationSeparationExponent (alpha : ℝ) :
    1 - 2 * (alpha - 1) / 3 = (5 - 2 * alpha) / 3 := by
  ring

/-- The strict Palasek packet window `alpha < 5/2` is exactly positivity of
`1-2(alpha-1)/3`, i.e. growth of `N epsilon`. -/
theorem localizationSeparationPositive (alpha : ℝ)
    (hα : alpha < 5 / 2) :
    0 < 1 - 2 * (alpha - 1) / 3 := by
  rw [localizationSeparationExponent]
  linarith

#check equalShell
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
