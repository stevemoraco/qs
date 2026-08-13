import Mathlib

namespace RHBraid

/-- The outer translation of the cascade is exactly the prescribed radius. -/
theorem cascade_outer_offset (H h : ℝ) : (H - h) + h = H := by
  ring

/-- Multiplying a real-spectrum weight by a factor in `[0,1]` preserves
nonnegativity and attenuates it. -/
theorem attenuation_product
    (j r x : ℝ)
    (hj0 : 0 ≤ j) (hjx : j ≤ x ^ 2)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ j * r ∧ j * r ≤ x ^ 2 := by
  constructor
  · exact mul_nonneg hj0 hr0
  · calc
      j * r ≤ j * 1 := mul_le_mul_of_nonneg_left hr1 hj0
      _ = j := by ring
      _ ≤ x ^ 2 := hjx

/-- The abstract reflected cascade factor is strictly negative whenever all
three geometric factors are nonzero.  In the analytic application these are
the support scale, `sinh`, and `cosh` factors. -/
theorem reflected_cascade_strict
    (H m s c : ℝ)
    (hH : H ≠ 0) (hm : m ≠ 0) (hs : s ≠ 0) (hc : c ≠ 0) :
    -(4 * m ^ 2 / H ^ 2 * s ^ 2 * c ^ 2) < 0 := by
  have hp : 0 < 4 * m ^ 2 / H ^ 2 * s ^ 2 * c ^ 2 := by
    positivity
  linarith

/-- A strict improvement at the positive square-root level gives a strict
improvement of the reflected energy amplitude. -/
theorem strict_square_amplification
    (outer cascade : ℝ)
    (houter : 0 ≤ outer) (hbetter : outer < cascade) :
    outer ^ 2 < cascade ^ 2 := by
  nlinarith

/-- The universal factor bound immediately yields the sharp reflected-energy
ceiling after multiplication by the nonnegative depth square. -/
theorem reflected_ceiling_from_factor
    (y r c : ℝ) (hr0 : 0 ≤ r) (hrc : r ≤ c ^ 2) :
    0 ≤ 4 * y ^ 2 * r ∧ 4 * y ^ 2 * r ≤ 4 * y ^ 2 * c ^ 2 := by
  constructor
  · positivity
  · exact mul_le_mul_of_nonneg_left hrc (by positivity)

/-- Substituting `a = H*y` into the support-normalized limiting amplitude
cancels the support scale exactly. -/
theorem ceiling_normalization
    (H y c : ℝ) (hH : H ≠ 0) :
    4 * (H * y * c) ^ 2 / H ^ 2 = 4 * y ^ 2 * c ^ 2 := by
  field_simp [hH]
  ring

/-- The factor-two cascade tie is the scalar content of the hyperbolic
double-angle identity once `sinh(a)=2*sinh(a/2)*cosh(a/2)` is supplied. -/
theorem factor_two_tie
    (s c : ℝ) :
    4 * (2 * s * c) ^ 2 = 16 * s ^ 2 * c ^ 2 := by
  ring

end RHBraid
