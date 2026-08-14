import Mathlib

open Filter Topology

/-!
# Yu fixed-filter unfiltering firewall

Finite real algebra and elementary sequential topology only.  These statements
isolate one exact obstruction, one reusable diagonal-selection inequality, and
the closedness of pairwise collinearity under pointwise filter removal.

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

/-- A vanishing planar minor is preserved by coordinatewise sequential limits.
This is the exact closedness statement needed when a sequence of filtered vector
pairs converges to the corresponding unfiltered pair. -/
theorem planar_minor_closed_under_limits
    (x1 y1 x2 y2 : ℕ → ℝ)
    (X1 Y1 X2 Y2 : ℝ)
    (hx1 : Tendsto x1 atTop (𝓝 X1))
    (hy1 : Tendsto y1 atTop (𝓝 Y1))
    (hx2 : Tendsto x2 atTop (𝓝 X2))
    (hy2 : Tendsto y2 atTop (𝓝 Y2))
    (hminor : ∀ n, x1 n * y2 n - y1 n * x2 n = 0) :
    X1 * Y2 - Y1 * X2 = 0 := by
  have hlim :
      Tendsto (fun n => x1 n * y2 n - y1 n * x2 n) atTop
        (𝓝 (X1 * Y2 - Y1 * X2)) :=
    (hx1.mul hy2).sub (hy1.mul hx2)
  have hlim0 :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
        (𝓝 (X1 * Y2 - Y1 * X2)) := by
    simpa only [hminor] using hlim
  exact tendsto_nhds_unique hlim0 tendsto_const_nhds

/-- Pointwise limits preserve all pairwise coordinate minors, even when the
one-dimensional line containing the filtered field is allowed to vary with the
filter index.  No common direction across filters is assumed. -/
theorem pairwise_minors_closed_under_pointwise_limits
    {α ι : Type*}
    (ω : ℕ → α → ι → ℝ)
    (Ω : α → ι → ℝ)
    (hconv : ∀ x i, Tendsto (fun n => ω n x i) atTop (𝓝 (Ω x i)))
    (hminor : ∀ n x y i j,
      ω n x i * ω n y j - ω n x j * ω n y i = 0) :
    ∀ x y i j,
      Ω x i * Ω y j - Ω x j * Ω y i = 0 := by
  intro x y i j
  exact planar_minor_closed_under_limits
    (fun n => ω n x i)
    (fun n => ω n x j)
    (fun n => ω n y i)
    (fun n => ω n y j)
    (Ω x i) (Ω x j) (Ω y i) (Ω y j)
    (hconv x i) (hconv x j) (hconv y i) (hconv y j)
    (fun n => hminor n x y i j)

#print axioms exact_coarse_average_is_axis_aligned
#print axioms unresolved_fine_pair_is_not_collinear
#print axioms unresolved_transverse_energy_survives
#print axioms perfect_fixed_filter_alignment_does_not_force_fine_alignment
#print axioms fixed_constant_can_be_absorbed_stagewise
#print axioms planar_minor_closed_under_limits
#print axioms pairwise_minors_closed_under_pointwise_limits

end NSYuMultifilterUnfilteringFirewall
