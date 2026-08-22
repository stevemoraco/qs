import Mathlib

/-!
# RH tent-ray finite algebra

Honesty label: finite algebra only. This file does not formalize the Weil
explicit formula, the Riemann zeta function, meromorphic continuation, Landau's
Laplace theorem, or RH.
-/

namespace MillenniumBraid.RHTentRayFinite

/-- The algebraic double-angle form of the squared tent filter. -/
theorem square_filter_identity (c : ℂ) :
    (1 - c) ^ 2 =
      (3 : ℂ) / 2 - 2 * c + ((2 * c ^ 2 - 1) / 2) := by
  ring

/-- Scaling algebra behind `a * hhat (a*z)` for the unit tent transform. -/
theorem tent_fourier_scaling
    (a z c : ℂ) (ha : a ≠ 0) (hz : z ≠ 0) :
    a * (2 * (1 - c) / (a * z) ^ 2) =
      2 * (1 - c) / (a * z ^ 2) := by
  field_simp [ha, hz]
  ring

/--
If a second-harmonic pole from `gamma` and a first-harmonic pole from
`2*gamma` coincide, this is their paired `±` residue coefficient.
-/
theorem paired_resonance_coefficient
    (mGamma mDouble gamma : ℂ) (hgamma : gamma ≠ 0) :
    2 * (mGamma / (4 * gamma ^ 4)) +
        2 * (-mDouble / (16 * gamma ^ 4)) =
      (4 * mGamma - mDouble) / (8 * gamma ^ 4) := by
  field_simp [hgamma]
  ring

/-- At a depth-maximal harmonic endpoint, the paired residue cannot vanish. -/
theorem endpoint_residue_ne_zero
    (m gamma : ℂ) (hm : m ≠ 0) (hgamma : gamma ≠ 0) :
    m / (2 * gamma ^ 4) ≠ 0 := by
  exact div_ne_zero hm (mul_ne_zero (by norm_num) (pow_ne_zero 4 hgamma))

/-- Polynomial normalization does not change a positive exponential exponent. -/
theorem rayleigh_sign_equiv
    (a T : ℝ) (ha : 0 < a) :
    0 ≤ 6 * T / a ^ 3 ↔ 0 ≤ T := by
  constructor
  · intro h
    have hpos : 0 < 6 / a ^ 3 := by positivity
    nlinarith [h]
  · intro h
    exact div_nonneg (mul_nonneg (by norm_num) h) (le_of_lt (by positivity : 0 < a ^ 3))

#print axioms MillenniumBraid.RHTentRayFinite.square_filter_identity
#print axioms MillenniumBraid.RHTentRayFinite.tent_fourier_scaling
#print axioms MillenniumBraid.RHTentRayFinite.paired_resonance_coefficient
#print axioms MillenniumBraid.RHTentRayFinite.endpoint_residue_ne_zero
#print axioms MillenniumBraid.RHTentRayFinite.rayleigh_sign_equiv

end MillenniumBraid.RHTentRayFinite
