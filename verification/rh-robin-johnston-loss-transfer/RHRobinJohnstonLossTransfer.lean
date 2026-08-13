import Mathlib

/-!
# Quantitative Robin--Johnston loss-transfer core

This file formalizes the order-theoretic and algebraic closure of the following
human analytic estimate for one prime cell.  If `R` is the Robin increment,
`J` the Johnston increment, `B >= 0` the midpoint-convexity buffer, `p > 0`,
and `L > 0`, then

`B - negPart J / (p * L^2) <= R`.

The theorems below prove, without any custom axiom, that this implies

`negPart R <= negPart J / (p * L^2)`

and, after the exact Johnston factorization `J = L*z`,

`negPart R <= negPart z / (p * L)`.

The calculus establishing the displayed prime-cell premise is deliberately not
smuggled into this module: it remains a separately auditable human dependency.
-/

namespace RHRobinJohnstonLossTransfer

/-- The negative part `x_- = max(-x, 0)`. -/
def negPart (x : ℝ) : ℝ := max (-x) 0

/-- A negative part is always nonnegative. -/
theorem negPart_nonneg (x : ℝ) : 0 ≤ negPart x := by
  exact le_max_right _ _

/-- Any lower bound `-q <= x`, with `q >= 0`, bounds the loss of `x` by `q`. -/
theorem negPart_le_of_lower_bound
    {x q : ℝ} (hq : 0 ≤ q) (hx : -q ≤ x) :
    negPart x ≤ q := by
  unfold negPart
  exact max_le (by linarith) hq

/-- Abstract buffered loss transfer. -/
theorem buffered_loss_transfer
    (robin johnstonLoss buffer weight : ℝ)
    (hj : 0 ≤ johnstonLoss)
    (hb : 0 ≤ buffer)
    (hw : 0 ≤ weight)
    (hcell : buffer - weight * johnstonLoss ≤ robin) :
    negPart robin ≤ weight * johnstonLoss := by
  apply negPart_le_of_lower_bound
  · exact mul_nonneg hw hj
  · linarith

/-- Prime-cell specialization with weight `1 / (p L^2)`. -/
theorem robin_loss_le_johnston_loss
    (robin johnston p L buffer : ℝ)
    (hp : 0 < p)
    (hL : 0 < L)
    (hbuffer : 0 ≤ buffer)
    (hcell : buffer - negPart johnston / (p * L^2) ≤ robin) :
    negPart robin ≤ negPart johnston / (p * L^2) := by
  have hden : 0 < p * L^2 := mul_pos hp (pow_pos hL 2)
  apply negPart_le_of_lower_bound
  · exact div_nonneg (negPart_nonneg johnston) hden.le
  · linarith

/-- A negative Robin increment can occur only after the convexity buffer is
strictly exhausted by the weighted Johnston loss. -/
theorem robin_negative_forces_budget_exhaustion
    (robin johnston p L buffer : ℝ)
    (hcell : buffer - negPart johnston / (p * L^2) ≤ robin)
    (hrobin : robin < 0) :
    buffer < negPart johnston / (p * L^2) := by
  linarith

/-- Negative parts commute with multiplication by a nonnegative scalar. -/
theorem negPart_mul_of_nonneg (a x : ℝ) (ha : 0 ≤ a) :
    negPart (a * x) = a * negPart x := by
  by_cases hx : 0 ≤ x
  · have hax : 0 ≤ a * x := mul_nonneg ha hx
    simp [negPart, hx, hax]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hax : a * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hx'
    simp only [negPart]
    rw [max_eq_left (neg_nonneg.mpr hax),
      max_eq_left (neg_nonneg.mpr hx')]
    ring

/-- Exact conversion of the Johnston loss weight under `J = L*z`. -/
theorem cocycle_weight_identity
    (z p L : ℝ) (hp : 0 < p) (hL : 0 < L) :
    negPart (L * z) / (p * L^2) = negPart z / (p * L) := by
  rw [negPart_mul_of_nonneg L z hL.le]
  field_simp [ne_of_gt hp, ne_of_gt hL] <;> ring

/-- The Robin loss is controlled directly by the weighted negative centered
prime-arrival state `z_- / (p L)`. -/
theorem robin_loss_le_centered_deficit
    (robin z p L buffer : ℝ)
    (hp : 0 < p)
    (hL : 0 < L)
    (hbuffer : 0 ≤ buffer)
    (hcell : buffer - negPart (L * z) / (p * L^2) ≤ robin) :
    negPart robin ≤ negPart z / (p * L) := by
  have h := robin_loss_le_johnston_loss
    robin (L * z) p L buffer hp hL hbuffer hcell
  rw [cocycle_weight_identity z p L hp hL] at h
  exact h

/-- Finite block summation preserves the buffered lower bound exactly. -/
theorem sum_buffered_lower_bound
    {ι : Type*} (s : Finset ι)
    (robin buffer charge : ι → ℝ)
    (hcell : ∀ i ∈ s, buffer i - charge i ≤ robin i) :
    (∑ i in s, buffer i) - (∑ i in s, charge i)
      ≤ ∑ i in s, robin i := by
  simpa only [Finset.sum_sub_distrib] using
    (Finset.sum_le_sum (fun i hi => hcell i hi))

/-- A strict finite block budget yields a positive final cumulative statistic. -/
theorem cumulative_positive_of_block_budget
    {ι : Type*} (s : Finset ι)
    (robin buffer charge : ι → ℝ)
    (initial final : ℝ)
    (hcell : ∀ i ∈ s, buffer i - charge i ≤ robin i)
    (hfinal : final = initial + ∑ i in s, robin i)
    (hbudget : ∑ i in s, charge i < initial + ∑ i in s, buffer i) :
    0 < final := by
  have hsum := sum_buffered_lower_bound s robin buffer charge hcell
  rw [hfinal]
  linarith

end RHRobinJohnstonLossTransfer
