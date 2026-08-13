import Mathlib

/-!
# Quantitative Robin--Johnston loss-transfer core

The strongest human one-cell estimate has the signed form

`buffer + johnston / (p * L^2) <= robin`.

The theorems below formalize its order-theoretic and algebraic closure.  In
particular, they prove the sharp loss bound, the coarser negative-part transfer,
the exact conversion under `johnston = L*z`, and finite signed block summation.

The calculus establishing the displayed one-cell premise is deliberately not
smuggled into this module: it remains a separately auditable human dependency.
-/

namespace RHRobinJohnstonLossTransfer

/-- The negative part `x_- = max(-x, 0)`. -/
def negPart (x : ℝ) : ℝ := max (-x) 0

/-- A negative part is always nonnegative. -/
theorem negPart_nonneg (x : ℝ) : 0 ≤ negPart x := by
  exact le_max_right _ _

/-- The negative part dominates `-x`. -/
theorem neg_le_negPart (x : ℝ) : -x ≤ negPart x := by
  unfold negPart
  exact le_max_left _ _

/-- Equivalently, `-x_- <= x`. -/
theorem neg_negPart_le (x : ℝ) : -negPart x ≤ x := by
  have h := neg_le_negPart x
  linarith

/-- Negative part reverses the ambient order. -/
theorem negPart_antitone {x y : ℝ} (hxy : x ≤ y) :
    negPart y ≤ negPart x := by
  unfold negPart
  exact max_le_max (neg_le_neg hxy) (le_refl 0)

/-- Any lower bound `-q <= x`, with `q >= 0`, bounds the loss of `x` by `q`. -/
theorem negPart_le_of_lower_bound
    {x q : ℝ} (hq : 0 ≤ q) (hx : -q ≤ x) :
    negPart x ≤ q := by
  unfold negPart
  exact max_le (by linarith) hq

/-- The sharp abstract loss transfer from an arbitrary lower bound. -/
theorem sharp_loss_transfer
    (robin lower : ℝ) (hcell : lower ≤ robin) :
    negPart robin ≤ negPart lower := by
  exact negPart_antitone hcell

/-- Abstract buffered loss transfer from a nonnegative charge. -/
theorem buffered_loss_transfer
    (robin charge buffer weight : ℝ)
    (hcharge : 0 ≤ charge)
    (hbuffer : 0 ≤ buffer)
    (hweight : 0 ≤ weight)
    (hcell : buffer - weight * charge ≤ robin) :
    negPart robin ≤ weight * charge := by
  apply negPart_le_of_lower_bound
  · exact mul_nonneg hweight hcharge
  · linarith

/-- A signed lower bound implies the corresponding negative-part lower bound. -/
theorem signed_lower_bound_implies_buffered_lower_bound
    (robin johnston buffer weight : ℝ)
    (hweight : 0 ≤ weight)
    (hcell : buffer + weight * johnston ≤ robin) :
    buffer - weight * negPart johnston ≤ robin := by
  have hj : -negPart johnston ≤ johnston := neg_negPart_le johnston
  have hmul : weight * (-negPart johnston) ≤ weight * johnston :=
    mul_le_mul_of_nonneg_left hj hweight
  calc
    buffer - weight * negPart johnston =
        buffer + weight * (-negPart johnston) := by ring
    _ ≤ buffer + weight * johnston := add_le_add_left hmul buffer
    _ ≤ robin := hcell

/-- Coarse loss transfer inherited from the stronger signed lower bound. -/
theorem signed_buffered_loss_transfer
    (robin johnston buffer weight : ℝ)
    (hbuffer : 0 ≤ buffer)
    (hweight : 0 ≤ weight)
    (hcell : buffer + weight * johnston ≤ robin) :
    negPart robin ≤ weight * negPart johnston := by
  exact buffered_loss_transfer robin (negPart johnston) buffer weight
    (negPart_nonneg johnston) hbuffer hweight
    (signed_lower_bound_implies_buffered_lower_bound
      robin johnston buffer weight hweight hcell)

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

/-- Exact conversion of the signed Johnston weight under `J = L*z`. -/
theorem cocycle_signed_weight_identity
    (z p L : ℝ) (hp : 0 < p) (hL : 0 < L) :
    (L * z) / (p * L^2) = z / (p * L) := by
  field_simp [ne_of_gt hp, ne_of_gt hL]

/-- Exact conversion of the Johnston loss weight under `J = L*z`. -/
theorem cocycle_weight_identity
    (z p L : ℝ) (hp : 0 < p) (hL : 0 < L) :
    negPart (L * z) / (p * L^2) = negPart z / (p * L) := by
  rw [negPart_mul_of_nonneg L z hL.le]
  field_simp [ne_of_gt hp, ne_of_gt hL]

/-- The signed prime-cell estimate is exactly the centered-state estimate. -/
theorem signed_prime_cell_to_centered_state
    (robin z p L buffer : ℝ)
    (hp : 0 < p)
    (hL : 0 < L)
    (hcell : buffer + (L * z) / (p * L^2) ≤ robin) :
    buffer + z / (p * L) ≤ robin := by
  rw [cocycle_signed_weight_identity z p L hp hL] at hcell
  exact hcell

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

/-- Finite block summation preserves a buffered lower bound exactly. -/
theorem sum_buffered_lower_bound
    {ι : Type*} (s : Finset ι)
    (robin buffer charge : ι → ℝ)
    (hcell : ∀ i ∈ s, buffer i - charge i ≤ robin i) :
    Finset.sum s buffer - Finset.sum s charge ≤ Finset.sum s robin := by
  simpa only [Finset.sum_sub_distrib] using
    (Finset.sum_le_sum (fun i hi => hcell i hi))

/-- Finite block summation preserves the stronger signed lower bound exactly. -/
theorem sum_signed_buffered_lower_bound
    {ι : Type*} (s : Finset ι)
    (robin buffer signed : ι → ℝ)
    (hcell : ∀ i ∈ s, buffer i + signed i ≤ robin i) :
    Finset.sum s buffer + Finset.sum s signed ≤ Finset.sum s robin := by
  simpa only [Finset.sum_add_distrib] using
    (Finset.sum_le_sum (fun i hi => hcell i hi))

/-- A strict finite charge budget yields a positive final cumulative statistic. -/
theorem cumulative_positive_of_block_budget
    {ι : Type*} (s : Finset ι)
    (robin buffer charge : ι → ℝ)
    (initial final : ℝ)
    (hcell : ∀ i ∈ s, buffer i - charge i ≤ robin i)
    (hfinal : final = initial + Finset.sum s robin)
    (hbudget : Finset.sum s charge < initial + Finset.sum s buffer) :
    0 < final := by
  have hsum := sum_buffered_lower_bound s robin buffer charge hcell
  rw [hfinal]
  linarith

/-- A strict signed finite-block lower bound yields positivity. -/
theorem cumulative_positive_of_signed_block_budget
    {ι : Type*} (s : Finset ι)
    (robin buffer signed : ι → ℝ)
    (initial final : ℝ)
    (hcell : ∀ i ∈ s, buffer i + signed i ≤ robin i)
    (hfinal : final = initial + Finset.sum s robin)
    (hbudget : 0 < initial + Finset.sum s buffer + Finset.sum s signed) :
    0 < final := by
  have hsum := sum_signed_buffered_lower_bound s robin buffer signed hcell
  rw [hfinal]
  linarith

end RHRobinJohnstonLossTransfer

#print axioms RHRobinJohnstonLossTransfer.negPart_antitone
#print axioms RHRobinJohnstonLossTransfer.sharp_loss_transfer
#print axioms RHRobinJohnstonLossTransfer.signed_lower_bound_implies_buffered_lower_bound
#print axioms RHRobinJohnstonLossTransfer.signed_buffered_loss_transfer
#print axioms RHRobinJohnstonLossTransfer.robin_loss_le_johnston_loss
#print axioms RHRobinJohnstonLossTransfer.robin_negative_forces_budget_exhaustion
#print axioms RHRobinJohnstonLossTransfer.negPart_mul_of_nonneg
#print axioms RHRobinJohnstonLossTransfer.cocycle_signed_weight_identity
#print axioms RHRobinJohnstonLossTransfer.cocycle_weight_identity
#print axioms RHRobinJohnstonLossTransfer.signed_prime_cell_to_centered_state
#print axioms RHRobinJohnstonLossTransfer.robin_loss_le_centered_deficit
#print axioms RHRobinJohnstonLossTransfer.sum_buffered_lower_bound
#print axioms RHRobinJohnstonLossTransfer.sum_signed_buffered_lower_bound
#print axioms RHRobinJohnstonLossTransfer.cumulative_positive_of_block_budget
#print axioms RHRobinJohnstonLossTransfer.cumulative_positive_of_signed_block_budget
