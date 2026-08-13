import Mathlib

namespace NSPressureCancelTriadSidebandFirewall

/-!
# Equal intended and conjugate-sideband coefficients

For the pressure-canceling carrier geometry, the low pump feeds an intended
high carrier with scalar numerator `2*K*n`, while real conjugate symmetry also
creates an off-packet sideband with numerator `-2*K*n`.  Their magnitudes are
identical, so the isolated triad has no perturbative sideband gain.

The surrounding Fourier/Leray identification is proved in the companion human
note.  This finite algebra does not prove or disprove Navier--Stokes.
-/

/-- Scalar numerator of the intended low-to-high feed. -/
def intendedNumerator (K n : ℝ) : ℝ := 2 * K * n

/-- Scalar numerator of the unavoidable conjugate sideband. -/
def sidebandNumerator (K n : ℝ) : ℝ := -2 * K * n

/-- The sideband is the negative of the intended feed. -/
theorem sideband_eq_neg_intended (K n : ℝ) :
    sidebandNumerator K n = - intendedNumerator K n := by
  simp [sidebandNumerator, intendedNumerator]

/-- Their coefficient magnitudes are exactly equal at every scale. -/
theorem abs_sideband_eq_abs_intended (K n : ℝ) :
    |sidebandNumerator K n| = |intendedNumerator K n| := by
  rw [sideband_eq_neg_intended]
  exact abs_neg _

/-- For positive carrier parameters, both magnitudes are nonzero. -/
theorem intended_abs_pos {K n : ℝ} (hK : 0 < K) (hn : 0 < n) :
    0 < |intendedNumerator K n| := by
  have hprod : 0 < intendedNumerator K n := by
    dsimp [intendedNumerator]
    positivity
  simpa [abs_of_pos hprod] using hprod

/-- Therefore the sideband cannot be strictly smaller than the intended feed. -/
theorem not_sideband_strictly_smaller {K n : ℝ}
    (hK : 0 < K) (hn : 0 < n) :
    ¬ |sidebandNumerator K n| < |intendedNumerator K n| := by
  rw [abs_sideband_eq_abs_intended]
  exact lt_irrefl _

/-- The exact amplitude ratio is one whenever the intended coefficient is
nonzero. -/
theorem sideband_ratio_eq_one {K n : ℝ}
    (hK : 0 < K) (hn : 0 < n) :
    |sidebandNumerator K n| / |intendedNumerator K n| = 1 := by
  rw [abs_sideband_eq_abs_intended]
  have hne : |intendedNumerator K n| ≠ 0 :=
    ne_of_gt (intended_abs_pos hK hn)
  exact div_self hne

/-- Every relevant output wavevector `(x,y,0)` is orthogonal to the visible
polarization `e₃=(0,0,1)`, so its `e₃` component survives Leray unchanged. -/
theorem planar_output_orthogonal_e3 (x y : ℝ) :
    x * 0 + y * 0 + 0 * 1 = 0 := by
  ring

#print axioms sideband_eq_neg_intended
#print axioms abs_sideband_eq_abs_intended
#print axioms intended_abs_pos
#print axioms not_sideband_strictly_smaller
#print axioms sideband_ratio_eq_one
#print axioms planar_output_orthogonal_e3

end NSPressureCancelTriadSidebandFirewall
