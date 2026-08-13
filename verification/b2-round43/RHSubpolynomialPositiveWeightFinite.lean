import Mathlib

/-!
# RH subpolynomial positive-weight finite spine

This file formalizes only finite ordered-field inequalities used in a weighted
positive-part audit. It does not define the Chebyshev function, the Riemann
zeta function, zeta zeros, integration, asymptotics, or the Riemann hypothesis.
-/

namespace MillenniumBraid
namespace B2Round43RH

/-- Positive part of a real scalar. -/
def positivePart (x : ℝ) : ℝ := max x 0

/-- Every scalar is bounded above by its positive part. -/
theorem self_le_positivePart (x : ℝ) : x ≤ positivePart x := by
  exact le_max_left x 0

/-- The positive part is nonnegative. -/
theorem positivePart_nonneg (x : ℝ) : 0 ≤ positivePart x := by
  exact le_max_right x 0

/-- Finite endpoint extraction.

If every event weight is at least the endpoint floor `w₀`, then weighted
positive-part mass dominates `w₀` times the signed mass. This is the finite
ordered-field spine of the monotone-weight step in the analytic proof. -/
theorem endpoint_weighted_positive_lower
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f weight : ι → ℝ) (w₀ : ℝ)
    (hw₀ : 0 ≤ w₀)
    (hweight : ∀ i ∈ s, w₀ ≤ weight i) :
    w₀ * (∑ i ∈ s, f i) ≤
      ∑ i ∈ s, weight i * positivePart (f i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hf : f i ≤ positivePart (f i) := self_le_positivePart (f i)
  have hp : 0 ≤ positivePart (f i) := positivePart_nonneg (f i)
  calc
    w₀ * f i ≤ w₀ * positivePart (f i) :=
      mul_le_mul_of_nonneg_left hf hw₀
    _ ≤ weight i * positivePart (f i) :=
      mul_le_mul_of_nonneg_right (hweight i hi) hp

/-- A positive signed spike survives endpoint extraction through a monotone
positive weight. -/
theorem positive_spike_survives_endpoint_weight
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f weight : ι → ℝ) (w₀ J : ℝ)
    (hw₀ : 0 ≤ w₀)
    (hweight : ∀ i ∈ s, w₀ ≤ weight i)
    (hJ : J ≤ ∑ i ∈ s, f i) :
    w₀ * J ≤ ∑ i ∈ s, weight i * positivePart (f i) := by
  calc
    w₀ * J ≤ w₀ * (∑ i ∈ s, f i) :=
      mul_le_mul_of_nonneg_left hJ hw₀
    _ ≤ ∑ i ∈ s, weight i * positivePart (f i) :=
      endpoint_weighted_positive_lower s f weight w₀ hw₀ hweight

/-- Once a vanishing damping exponent is at most half a fixed positive
horizontal-zero margin, at least half the margin survives. -/
theorem half_margin_survives_vanishing_exponent
    {δ η q : ℝ}
    (hmargin : η < δ)
    (hq : q ≤ (δ - η) / 2) :
    0 < δ - η - q ∧ (δ - η) / 2 ≤ δ - η - q := by
  constructor <;> linarith

/-- Scalar rewrite behind `x^(δ-η) x^(-q) = x^(δ-η-q)` at the exponent
level. The real-power law itself is intentionally outside this finite file. -/
theorem exponent_regroup (δ η q : ℝ) :
    (δ - η) + (-q) = δ - η - q := by
  ring

/-- If a nonnegative partial-mass sequence is unbounded along a subsequence,
then it cannot be bounded by a fixed constant. This logical shell avoids any
silent subsequence-to-limit upgrade. -/
theorem unbounded_subsequence_refutes_global_bound
    {α : Type*} (mass : α → ℝ) (B : ℝ)
    (hspike : ∃ i, B < mass i) :
    ¬ ∀ i, mass i ≤ B := by
  rintro hall
  obtain ⟨i, hi⟩ := hspike
  exact (not_lt_of_ge (hall i)) hi

#print axioms self_le_positivePart
#print axioms positivePart_nonneg
#print axioms endpoint_weighted_positive_lower
#print axioms positive_spike_survives_endpoint_weight
#print axioms half_margin_survives_vanishing_exponent
#print axioms exponent_regroup
#print axioms unbounded_subsequence_refutes_global_bound

end B2Round43RH
end MillenniumBraid
