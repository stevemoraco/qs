import Mathlib

/-!
# Faizal–Shabir weak analytic-coordinate firewall

Finite scalar facts behind C230.  The audited source uses both an interaction
analytic in `g` near zero and an effective-action coefficient proportional to
`1 / g^2`.  These declarations do **not** formalize Yang–Mills.  They record why
an explicit coupling-dependent field/coordinate rescaling is load-bearing and
show, at scalar level, how such a rescaling can remove the apparent singularity.
-/

namespace Millennium.YangMills.FaizalShabirWeakAnalyticCoordinateFirewall

/-- A fixed candidate bound `C` is smaller than `1/g^2` whenever `g` is small
enough that `C g^2 < 1`. -/
theorem inverse_square_exceeds_fixed_candidate
    (C g : ℝ)
    (hg : 0 < g)
    (hsmall : C * g ^ 2 < 1) :
    C < 1 / g ^ 2 := by
  have hg2 : 0 < g ^ 2 := sq_pos_of_pos hg
  exact (lt_div_iff₀ hg2).2 (by simpa [mul_comm] using hsmall)

/-- Conversely, dominating the inverse-square coefficient forces the natural
scaled lower bound `1 ≤ C g^2`. -/
theorem inverse_square_bound_forces_scaled_unit
    (C g : ℝ)
    (hg : 0 < g)
    (hbound : 1 / g ^ 2 ≤ C) :
    1 ≤ C * g ^ 2 := by
  have hg2 : 0 < g ^ 2 := sq_pos_of_pos hg
  have := (div_le_iff₀ hg2).1 hbound
  simpa [mul_comm] using this

/-- A scalar field rescaling `A = g B` exactly cancels the inverse-square
quadratic coefficient. -/
theorem field_rescaling_cancels_inverse_square
    (g B : ℝ)
    (hg : g ≠ 0) :
    (1 / g ^ 2) * (g * B) ^ 2 = B ^ 2 := by
  field_simp [hg]

/-- The same cancellation with the conventional factor `1/4`. -/
theorem quarter_field_rescaling_cancels_inverse_square
    (g B : ℝ)
    (hg : g ≠ 0) :
    (1 / (4 * g ^ 2)) * (g * B) ^ 2 = B ^ 2 / 4 := by
  field_simp [hg]

/-- Scalar shadow of the curvature identity
`F(g B) = g X + g^2 Y = g (X + g Y)`: after the weak-field rescaling,
the inverse-square quadratic normalization becomes polynomial in `g`. -/
theorem nonlinear_field_rescaling_cancels_inverse_square
    (g X Y : ℝ)
    (hg : g ≠ 0) :
    (1 / g ^ 2) * (g * X + g ^ 2 * Y) ^ 2 = (X + g * Y) ^ 2 := by
  field_simp [hg]

/-- Conventional quarter-normalized version of the nonlinear rescaling. -/
theorem quarter_nonlinear_field_rescaling_cancels_inverse_square
    (g X Y : ℝ)
    (hg : g ≠ 0) :
    (1 / (4 * g ^ 2)) * (g * X + g ^ 2 * Y) ^ 2 = (X + g * Y) ^ 2 / 4 := by
  field_simp [hg]

#print axioms inverse_square_exceeds_fixed_candidate
#print axioms inverse_square_bound_forces_scaled_unit
#print axioms field_rescaling_cancels_inverse_square
#print axioms quarter_field_rescaling_cancels_inverse_square
#print axioms nonlinear_field_rescaling_cancels_inverse_square
#print axioms quarter_nonlinear_field_rescaling_cancels_inverse_square

end Millennium.YangMills.FaizalShabirWeakAnalyticCoordinateFirewall
