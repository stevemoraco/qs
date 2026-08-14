import Mathlib

/-!
# Yu fixed-filter unfiltering firewall

Finite real algebra only.  These statements isolate one exact obstruction and
one reusable diagonal-selection inequality for the filtered-vorticity route.

They do **not** formalize Runlong Yu's PDE estimates, mollifier convergence,
Giga--Miura's Type-I theorem, ancient-profile extraction, Navier--Stokes
regularity, or blow-up.
-/

namespace NSYuMultifilterUnfilteringFirewall

/-- Two unresolved fine vectors can have a perfectly axis-aligned equal-weight
coarse average. -/
theorem exact_coarse_average_is_axis_aligned :
    (((1 : ℝ) + 1) / 2 = 1) ∧
    (((1 : ℝ) + (-1)) / 2 = 0) := by
  norm_num

/-- The same two fine vectors are not collinear: their planar determinant is
exactly `-2`. -/
theorem unresolved_fine_pair_is_not_collinear :
    (1 : ℝ) * (-1) - 1 * 1 = -2 := by
  norm_num

/-- Their unresolved transverse components carry strictly positive quadratic
mass even though they cancel in the coarse average. -/
theorem unresolved_transverse_energy_survives :
    (1 : ℝ) ^ 2 + (-1 : ℝ) ^ 2 = 2 := by
  norm_num

/-- Minimal no-free-lunch model: perfect alignment of one fixed coarse average
does not force the underlying fine vectors to share a line. -/
theorem perfect_fixed_filter_alignment_does_not_force_fine_alignment :
    ∃ x1 y1 x2 y2 : ℝ,
      (x1 + x2) / 2 = 1 ∧
      (y1 + y2) / 2 = 0 ∧
      x1 * y2 - y1 * x2 ≠ 0 := by
  refine ⟨1, 1, 1, -1, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num

/-- For every fixed positive conditioning constant, an error can be selected
small enough to beat any prescribed positive tolerance.  This is the finite
algebra behind a post-limit countable filter diagonal: constants may depend on
the fixed filter index; they need not be uniformly bounded across all filters. -/
theorem fixed_constant_can_be_absorbed_stagewise
    (C delta : ℝ) (hC : 0 < C) (hdelta : 0 < delta) :
    let e := delta / (2 * C)
    0 < e ∧ C * e < delta := by
  dsimp
  constructor
  · positivity
  · have hC0 : C ≠ 0 := ne_of_gt hC
    have hhalf : delta / 2 < delta := by linarith
    calc
      C * (delta / (2 * C)) = delta / 2 := by field_simp [hC0]
      _ < delta := hhalf

#print axioms exact_coarse_average_is_axis_aligned
#print axioms unresolved_fine_pair_is_not_collinear
#print axioms unresolved_transverse_energy_survives
#print axioms perfect_fixed_filter_alignment_does_not_force_fine_alignment
#print axioms fixed_constant_can_be_absorbed_stagewise

end NSYuMultifilterUnfilteringFirewall
