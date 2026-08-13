import Mathlib

/-!
# Finite weak-tail spine for the prime-entry zero-depth law

This file formalizes the finite first-moment/weak-tail inequality used in the
human analytic B52C theorem.  For nonnegative weights `w i` and nonnegative
values `x i`, the weighted mass above a threshold is controlled by the first
moment.  A normalized corollary has exactly the scalar shape used for the
ordinary-prime endpoint tail at `r = 1`.

This file does **not** formalize primes, Chebyshev functions, the dyadic queue,
layer cake, zeta zeros, limsup asymptotics, B50, B52C, or RH.
-/

namespace Millennium.RH.PrimeEntryWeakTailFinite

open Finset BigOperators

noncomputable section

variable {ι : Type*}

/-- Weighted mass of the finite set on which `x` exceeds `threshold`. -/
def tailWeight (s : Finset ι) (w x : ι → ℝ) (threshold : ℝ) : ℝ :=
  ∑ i in s.filter (fun i => threshold < x i), w i

/-- Weighted first moment of a finite nonnegative family. -/
def firstMoment (s : Finset ι) (w x : ι → ℝ) : ℝ :=
  ∑ i in s, w i * x i

/--
Finite weighted Markov inequality in the exact strict-tail convention used by
B52C.  No sign assumption on the threshold is needed.
-/
theorem threshold_mul_tailWeight_le_firstMoment
    (s : Finset ι) (w x : ι → ℝ) (threshold : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    threshold * tailWeight s w x threshold ≤ firstMoment s w x := by
  classical
  unfold tailWeight firstMoment
  calc
    threshold * (∑ i in s.filter (fun i => threshold < x i), w i) =
        ∑ i in s.filter (fun i => threshold < x i), threshold * w i := by
          rw [Finset.mul_sum]
    _ ≤ ∑ i in s.filter (fun i => threshold < x i), w i * x i := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_filter.mp hi
      have hwi : 0 ≤ w i := hw i hi'.1
      have htx : threshold ≤ x i := le_of_lt hi'.2
      have hmul : threshold * w i ≤ x i * w i :=
        mul_le_mul_of_nonneg_right htx hwi
      simpa [mul_comm] using hmul
    _ ≤ ∑ i in s, w i * x i := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset (fun i => threshold < x i) s)
        (by
          intro i hiS hiNotTail
          exact mul_nonneg (hw i hiS) (hx i hiS))

/-- Divide a threshold-moment inequality by a positive square-root scale. -/
theorem normalized_tail_le_normalized_moment
    {Y threshold A M : ℝ}
    (hY : 0 < Y)
    (h : threshold * Real.sqrt Y * A ≤ M) :
    threshold * A ≤ M / Real.sqrt Y := by
  have hsqrt : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY
  apply (le_div_iff₀ hsqrt).2
  calc
    threshold * A * Real.sqrt Y =
        threshold * Real.sqrt Y * A := by ring
    _ ≤ M := h

/--
Direct finite `r = 1` block-tail estimate.  In the prime application one takes
`x i = [E(p_i)]₊`, `w i = log p_i`, and scale `Y`.
-/
theorem scaled_threshold_tail_le_firstMoment
    (s : Finset ι) (w x : ι → ℝ) {Y threshold : ℝ}
    (hY : 0 < Y)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    threshold * tailWeight s w x (threshold * Real.sqrt Y) ≤
      firstMoment s w x / Real.sqrt Y := by
  apply normalized_tail_le_normalized_moment hY
  exact threshold_mul_tailWeight_le_firstMoment
    s w x (threshold * Real.sqrt Y) hw hx

/-- Remove a fixed endpoint cost from a one-sided moment transfer. -/
theorem fixed_cost_subtraction
    {blockMoment primeMoment endpointCost : ℝ}
    (h : blockMoment ≤ endpointCost + primeMoment) :
    blockMoment - endpointCost ≤ primeMoment := by
  linarith

#print axioms threshold_mul_tailWeight_le_firstMoment
#print axioms normalized_tail_le_normalized_moment
#print axioms scaled_threshold_tail_le_firstMoment
#print axioms fixed_cost_subtraction

end

end Millennium.RH.PrimeEntryWeakTailFinite
