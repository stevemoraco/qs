import Mathlib

namespace Millennium.YangMills.FaizalShabirWhitenedShellSourceFirewall

/-- Scalar shadow of `phi = A xi`: the physical Gaussian variance carries the
square of the shell factor. -/
theorem physicalVarianceFactor (a x : ℝ) :
    (a * x) ^ 2 = a ^ 2 * x ^ 2 := by
  ring

/-- Centering the whitened shell variable is sufficient to center the physical
fluctuation obtained from it by a linear shell factor. -/
theorem physicalMeanZeroOfWhitenedMeanZero (a m : ℝ) (hm : m = 0) :
    a * m = 0 := by
  simp [hm]

/-- Finite shadow of the perturbative coercivity argument: if the whitened
source Hessian differs from `1` by at most `delta`, then it is bounded below by
`1-delta`. -/
theorem whitenedHessianLowerBound (h delta : ℝ)
    (hpert : |h - 1| ≤ delta) :
    1 - delta ≤ h := by
  rw [abs_le] at hpert
  linarith [hpert.1]

/-- Cross-multiplied Schur-complement invariance under a nonzero linear source
rescaling `j = r k`: both numerator and denominator acquire the same `r^2`.
This is the finite algebraic reason whitening changes conditioning but not the
stationary background quadratic coefficient. -/
theorem schurNumeratorSourceRescale (a b h r : ℝ) :
    (a * h - b ^ 2) * r ^ 2 = a * (h * r ^ 2) - (b * r) ^ 2 := by
  ring

end Millennium.YangMills.FaizalShabirWhitenedShellSourceFirewall
