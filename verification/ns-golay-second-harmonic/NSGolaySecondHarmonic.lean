import Mathlib

/-!
# Reflected-helicity cancellation of the `2d` secondary harmonic

This file formalizes only:

* the exact reflected cross-frequency sum;
* vanishing of a same-eigenvalue coefficient;
* collapse of the geometric derivative from `Q` to the lower scale `d`;
* exact cancellation of two reflected opposite-helicity scalar channels;
* failure of one-channel truncation; and
* the symmetry-defect residual estimate.

It does not formalize complex helical vectors, Fourier packets, the
Navier--Stokes bilinear operator, heat flow, shadowing, or blow-up.
-/

namespace NSGolaySecondHarmonic

/-- BANKER: the reflected cross frequencies `d+p` and `d-p` sum exactly to
`2d`. -/
theorem reflected_cross_modes_sum
    {G : Type*} [AddCommGroup G] (d p : G) :
    (d + p) + (d - p) = d + d := by
  abel

/-- Same-helicity equal-radius inputs have zero signed-eigenvalue difference. -/
theorem same_eigenvalue_difference_zero (s Q : ℝ) :
    s * Q - s * Q = 0 := by
  ring

/-- The apparent parent derivative `Q` collapses to the lower scale `d`
when the reflected geometry satisfies `Q cos(beta)=d`. -/
theorem reflected_derivative_collapses_to_lower_scale
    (Q sinBeta cosBeta d : ℝ) (hgeom : Q * cosBeta = d) :
    Q * sinBeta * cosBeta = d * sinBeta := by
  calc
    Q * sinBeta * cosBeta = (Q * cosBeta) * sinBeta := by ring
    _ = d * sinBeta := by rw [hgeom]

/-- BANKER/CLEANER: if reflected source amplitudes have the forms
`a(1+sR)` and `-b(1+sR)`, the two opposite-helicity return channels cancel
exactly. -/
theorem reflected_opposite_helicity_channels_cancel
    (a b R B : ℝ) :
    B * (a * (1 + R)) * (-b * (1 - R)) +
        (-B) * (a * (1 - R)) * (-b * (1 + R)) = 0 := by
  ring

/-- CRITIC: retaining only one opposite-helicity channel need not cancel. -/
theorem one_channel_truncation_leaves_nonzero_residual :
    (1 : ℝ) * (1 * (1 + 0)) * (-1 * (1 - 0)) = -1 := by
  norm_num

/-- Packet-level symmetry defects enter linearly: if the reflected channel
products differ by at most `epsilon`, the residual is bounded by
`|B| epsilon`. -/
theorem reflected_channel_symmetry_error_bound
    (B Pplus Pminus epsilon : ℝ)
    (herror : |Pplus - Pminus| ≤ epsilon) :
    |B * Pplus - B * Pminus| ≤ |B| * epsilon := by
  calc
    |B * Pplus - B * Pminus| = |B * (Pplus - Pminus)| := by ring
    _ = |B| * |Pplus - Pminus| := abs_mul _ _
    _ ≤ |B| * epsilon :=
      mul_le_mul_of_nonneg_left herror (abs_nonneg B)

#print axioms reflected_cross_modes_sum
#print axioms same_eigenvalue_difference_zero
#print axioms reflected_derivative_collapses_to_lower_scale
#print axioms reflected_opposite_helicity_channels_cancel
#print axioms one_channel_truncation_leaves_nonzero_residual
#print axioms reflected_channel_symmetry_error_bound

end NSGolaySecondHarmonic
