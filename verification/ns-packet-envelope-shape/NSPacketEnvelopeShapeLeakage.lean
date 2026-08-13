import Mathlib

/-!
# Fixed-envelope packet shape leakage

This file formalizes the scalar algebra behind the exact orthogonal projection
of the leading localized packet product profile `φ_B²` onto the marked profile
`φ_B`.

After the analytic change of variables, the relevant moments are

* marked squared norm: `B³ μ₃²`;
* total product squared norm: `B³ μ₄`;
* orthogonal residual squared norm: `B³ (μ₄ - μ₃²)`.

The analytic theorem that a fixed nonzero smooth compact bump has
`μ₃² < μ₄` is kept outside this finite algebra file.  No PDE conclusion is
encoded here.
-/

namespace NSPacketEnvelopeShapeLeakage

/-- Squared norm of the marked one-profile projection. -/
def markedSq (B μ₃ : ℝ) : ℝ := B ^ 3 * μ₃ ^ 2

/-- Squared norm of the orthogonal product-profile residual. -/
def residualSq (B μ₃ μ₄ : ℝ) : ℝ := B ^ 3 * (μ₄ - μ₃ ^ 2)

/-- Exact Pythagorean split of the scaled fourth moment. -/
theorem total_profile_split (B μ₃ μ₄ : ℝ) :
    B ^ 3 * μ₄ = markedSq B μ₃ + residualSq B μ₃ μ₄ := by
  unfold markedSq residualSq
  ring

/-- A positive fixed moment gap gives a positive residual at every positive
concentration scale. -/
theorem residualSq_pos
    {B μ₃ μ₄ : ℝ}
    (hB : 0 < B)
    (hgap : μ₃ ^ 2 < μ₄) :
    0 < residualSq B μ₃ μ₄ := by
  unfold residualSq
  have hB3 : 0 < B ^ 3 := by positivity
  have hdiff : 0 < μ₄ - μ₃ ^ 2 := sub_pos.mpr hgap
  positivity

/-- The residual-to-marked squared ratio is independent of the concentration
scale `B` whenever the marked moment is nonzero. -/
theorem fixed_residual_to_marked_ratio
    {B μ₃ μ₄ : ℝ}
    (hμ₃ : μ₃ ≠ 0) :
    residualSq B μ₃ μ₄ =
      ((μ₄ - μ₃ ^ 2) / μ₃ ^ 2) * markedSq B μ₃ := by
  unfold residualSq markedSq
  have hsq : μ₃ ^ 2 ≠ 0 := pow_ne_zero 2 hμ₃
  field_simp

/-- The same identity written without division: concentration multiplies the
marked and residual channels by the same factor. -/
theorem common_concentration_factor (B μ₃ μ₄ : ℝ) :
    μ₃ ^ 2 * residualSq B μ₃ μ₄ =
      (μ₄ - μ₃ ^ 2) * markedSq B μ₃ := by
  unfold residualSq markedSq
  ring

/-- Under a positive moment gap and a nonzero marked moment, both squared
channels are positive at every positive concentration scale. -/
theorem marked_and_residual_both_pos
    {B μ₃ μ₄ : ℝ}
    (hB : 0 < B)
    (hμ₃ : μ₃ ≠ 0)
    (hgap : μ₃ ^ 2 < μ₄) :
    0 < markedSq B μ₃ ∧ 0 < residualSq B μ₃ μ₄ := by
  constructor
  · unfold markedSq
    have hB3 : 0 < B ^ 3 := by positivity
    have hμsq : 0 < μ₃ ^ 2 := sq_pos_of_ne_zero hμ₃
    positivity
  · exact residualSq_pos hB hgap

/-- If the residual is zero at a positive scale, then the moment gap itself is
zero.  Increasing concentration cannot erase a fixed nonzero gap. -/
theorem residual_zero_iff_moment_gap_zero
    {B μ₃ μ₄ : ℝ}
    (hB : B ≠ 0) :
    residualSq B μ₃ μ₄ = 0 ↔ μ₄ = μ₃ ^ 2 := by
  unfold residualSq
  constructor
  · intro h
    have hB3 : B ^ 3 ≠ 0 := pow_ne_zero 3 hB
    have hdiff : μ₄ - μ₃ ^ 2 = 0 := (mul_eq_zero.mp h).resolve_left hB3
    linarith
  · intro h
    rw [h]
    ring

#print axioms total_profile_split
#print axioms residualSq_pos
#print axioms fixed_residual_to_marked_ratio
#print axioms common_concentration_factor
#print axioms marked_and_residual_both_pos
#print axioms residual_zero_iff_moment_gap_zero

end NSPacketEnvelopeShapeLeakage
