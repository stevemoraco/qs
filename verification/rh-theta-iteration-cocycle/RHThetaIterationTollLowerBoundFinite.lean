import Mathlib

/-!
# RH theta-iteration quantitative toll finite core

HONESTY BOUNDARY

This file verifies only finite real algebra used by the paper-level theta-orbit
analysis:

* two scalar lower bounds for the descending and increasing interval brackets;
* two finite weighted-sum lower bounds by the square of the interval mass;
* a strict-positive-toll trajectory whose state remains negative forever at
  the finite algebraic level.

It does not formalize primes, the Chebyshev theta function, square roots of
actual prime-prefix states, integrals, infinite series, Run49's depth theorem,
zeta zeros, RH, or an official Clay statement.
-/

namespace MillenniumBraid
namespace RHThetaIterationTollLowerBoundFinite

open Finset

/-- Quantitative descending bracket bound. -/
theorem descending_bracket_lower_bound
    {a b r : ℝ}
    (ha : 0 < a)
    (hb : 0 ≤ b)
    (hba : b ≤ a)
    (hr : r ≤ 1 / a) :
    (a ^ 2 - b ^ 2) / (a * (a + b) ^ 2) ≤
      2 / (a + b) - r := by
  have hab : 0 < a + b := add_pos_of_pos_of_nonneg ha hb
  have hid :
      (a ^ 2 - b ^ 2) / (a * (a + b) ^ 2) =
        2 / (a + b) - 1 / a := by
    field_simp [ne_of_gt ha, ne_of_gt hab]
    ring
  rw [hid]
  linarith

/-- Quantitative increasing bracket bound. -/
theorem increasing_bracket_lower_bound
    {a b r : ℝ}
    (ha : 0 < a)
    (hab : a ≤ b)
    (hr : 1 / a ≤ r) :
    (b ^ 2 - a ^ 2) / (a * (a + b) ^ 2) ≤
      r - 2 / (a + b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have habpos : 0 < a + b := add_pos ha hb
  have hid :
      (b ^ 2 - a ^ 2) / (a * (a + b) ^ 2) =
        1 / a - 2 / (a + b) := by
    field_simp [ne_of_gt ha, ne_of_gt habpos]
    ring
  rw [hid]
  linarith

/-- Nonnegative descending atoms with total mass `a²-b²` pay at least the
square-mass critical toll. -/
theorem descending_weighted_toll_lower_bound
    {ι : Type*}
    (s : Finset ι)
    (w r : ι → ℝ)
    {a b : ℝ}
    (ha : 0 < a)
    (hb : 0 ≤ b)
    (hba : b ≤ a)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hr : ∀ i ∈ s, r i ≤ 1 / a)
    (hmass : ∑ i ∈ s, w i = a ^ 2 - b ^ 2) :
    (a ^ 2 - b ^ 2) ^ 2 / (a * (a + b) ^ 2) ≤
      ∑ i ∈ s, w i * (2 / (a + b) - r i) := by
  let c : ℝ := (a ^ 2 - b ^ 2) / (a * (a + b) ^ 2)
  have hpoint :
      ∀ i ∈ s, w i * c ≤ w i * (2 / (a + b) - r i) := by
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (descending_bracket_lower_bound ha hb hba (hr i hi))
      (hw i hi)
  calc
    (a ^ 2 - b ^ 2) ^ 2 / (a * (a + b) ^ 2) =
        ∑ i ∈ s, w i * c := by
          rw [← Finset.sum_mul, hmass]
          simp only [c]
          ring
    _ ≤ ∑ i ∈ s, w i * (2 / (a + b) - r i) :=
      Finset.sum_le_sum hpoint

/-- Nonnegative increasing atoms with total mass `b²-a²` pay at least the
square-mass critical toll. -/
theorem increasing_weighted_toll_lower_bound
    {ι : Type*}
    (s : Finset ι)
    (w r : ι → ℝ)
    {a b : ℝ}
    (ha : 0 < a)
    (hab : a ≤ b)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hr : ∀ i ∈ s, 1 / a ≤ r i)
    (hmass : ∑ i ∈ s, w i = b ^ 2 - a ^ 2) :
    (b ^ 2 - a ^ 2) ^ 2 / (a * (a + b) ^ 2) ≤
      ∑ i ∈ s, w i * (r i - 2 / (a + b)) := by
  let c : ℝ := (b ^ 2 - a ^ 2) / (a * (a + b) ^ 2)
  have hpoint :
      ∀ i ∈ s, w i * c ≤ w i * (r i - 2 / (a + b)) := by
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (increasing_bracket_lower_bound ha hab (hr i hi))
      (hw i hi)
  calc
    (b ^ 2 - a ^ 2) ^ 2 / (a * (a + b) ^ 2) =
        ∑ i ∈ s, w i * c := by
          rw [← Finset.sum_mul, hmass]
          simp only [c]
          ring
    _ ≤ ∑ i ∈ s, w i * (r i - 2 / (a + b)) :=
      Finset.sum_le_sum hpoint

/-- A simple adverse state on the unbounded translation orbit. -/
def adverseState (x : ℝ) : ℝ := -1 + 1 / (x + 2)

/-- The exact positive step toll for `x ↦ x+1`. -/
def adverseToll (x : ℝ) : ℝ := 1 / ((x + 2) * (x + 3))

/-- The adverse state satisfies an exact strict-toll recurrence. -/
theorem adverse_step_identity
    {x : ℝ}
    (hx : 0 ≤ x) :
    adverseState x = adverseState (x + 1) + adverseToll x := by
  have h2 : x + 2 ≠ 0 := ne_of_gt (by linarith)
  have h3 : x + 3 ≠ 0 := ne_of_gt (by linarith)
  simp only [adverseState, adverseToll]
  field_simp [h2, h3]
  ring

/-- Every state on the nonnegative half-line remains strictly adverse. -/
theorem adverse_state_negative
    {x : ℝ}
    (hx : 0 ≤ x) :
    adverseState x < 0 := by
  have hden : 0 < x + 2 := by linarith
  have hfrac : 1 / (x + 2) < 1 := by
    apply (div_lt_iff₀ hden).2
    linarith
  simp only [adverseState]
  linarith

/-- Every step toll is strictly positive. -/
theorem adverse_toll_positive
    {x : ℝ}
    (hx : 0 ≤ x) :
    0 < adverseToll x := by
  have h2 : 0 < x + 2 := by linarith
  have h3 : 0 < x + 3 := by linarith
  exact one_div_pos.mpr (mul_pos h2 h3)

/-- Strict positive toll along an unbounded translation orbit does not force
positivity of the state. -/
theorem strict_toll_with_negative_next_state
    {x : ℝ}
    (hx : 0 ≤ x) :
    adverseState (x + 1) < adverseState x ∧
      adverseState (x + 1) < 0 := by
  constructor
  · have hstep := adverse_step_identity hx
    have htoll := adverse_toll_positive hx
    linarith
  · exact adverse_state_negative (by linarith)

#print axioms descending_bracket_lower_bound
#print axioms increasing_bracket_lower_bound
#print axioms descending_weighted_toll_lower_bound
#print axioms increasing_weighted_toll_lower_bound
#print axioms adverse_step_identity
#print axioms adverse_state_negative
#print axioms adverse_toll_positive
#print axioms strict_toll_with_negative_next_state

end RHThetaIterationTollLowerBoundFinite
end MillenniumBraid
