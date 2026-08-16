import Mathlib

open scoped BigOperators

/-!
# NS Yu diffuse-kernel decoupling finite core

Finite positive-kernel inequalities used by the Hardy-Dini diffuse branch.
These statements do not formalize Navier--Stokes, Yu's PDE quantities, or a
Millennium conclusion.
-/

namespace NSYuDiffuseKernelDecoupling

/-- A mass distribution capped pointwise by `δ` has at most `card(s) * δ`
inside any finite window `s`. -/
theorem finite_window_mass_le_card_mul_cap
    {ι : Type*} (s : Finset ι) (p : ι → ℝ) (δ : ℝ)
    (hp : ∀ i ∈ s, p i ≤ δ) :
    (∑ i ∈ s, p i) ≤ (s.card : ℝ) * δ := by
  calc
    (∑ i ∈ s, p i) ≤ ∑ i ∈ s, δ := by
      exact Finset.sum_le_sum (fun i hi => hp i hi)
    _ = (s.card : ℝ) * δ := by simp

/-- If one factor is capped by `δ` and the other has total mass at most `Q`,
their positive diagonal pairing is at most `δ Q`. -/
theorem capped_pairing_le_cap_mul_total
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (δ Q : ℝ)
    (hδ : 0 ≤ δ)
    (hp : ∀ i, p i ≤ δ)
    (hq : ∀ i, 0 ≤ q i)
    (hQ : (∑ i, q i) ≤ Q) :
    (∑ i, p i * q i) ≤ δ * Q := by
  calc
    (∑ i, p i * q i) ≤ ∑ i, δ * q i := by
      exact Finset.sum_le_sum
        (fun i _ => mul_le_mul_of_nonneg_right (hp i) (hq i))
    _ = δ * ∑ i, q i := by
      simp [Finset.mul_sum]
    _ ≤ δ * Q := mul_le_mul_of_nonneg_left hQ hδ

/-- A positive interaction kernel with bounded column mass cannot sustain an
order-one interaction against a diffuse capped probability cloud and a second
currency of bounded total mass. -/
theorem bounded_column_kernel_pairing
    {ι : Type*} [Fintype ι]
    (p b : ι → ℝ) (W : ι → ι → ℝ)
    (δ K B : ℝ)
    (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hp : ∀ i, p i ≤ δ)
    (hb : ∀ j, 0 ≤ b j)
    (hW : ∀ i j, 0 ≤ W i j)
    (hcol : ∀ j, (∑ i, W i j) ≤ K)
    (hB : (∑ j, b j) ≤ B) :
    (∑ i, ∑ j, p i * W i j * b j) ≤ δ * K * B := by
  have hinner : ∀ j, (∑ i, p i * W i j) ≤ δ * K := by
    intro j
    calc
      (∑ i, p i * W i j) ≤ ∑ i, δ * W i j := by
        exact Finset.sum_le_sum
          (fun i _ => mul_le_mul_of_nonneg_right (hp i) (hW i j))
      _ = δ * ∑ i, W i j := by
        simp [Finset.mul_sum]
      _ ≤ δ * K := mul_le_mul_of_nonneg_left (hcol j) hδ
  calc
    (∑ i, ∑ j, p i * W i j * b j)
        = ∑ j, b j * (∑ i, p i * W i j) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j hj
            simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
    _ ≤ ∑ j, b j * (δ * K) := by
      exact Finset.sum_le_sum
        (fun j _ => mul_le_mul_of_nonneg_left (hinner j) (hb j))
    _ = (δ * K) * (∑ j, b j) := by
      simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
    _ ≤ (δ * K) * B :=
      mul_le_mul_of_nonneg_left hB (mul_nonneg hδ hK)
    _ = δ * K * B := by ring

#print axioms finite_window_mass_le_card_mul_cap
#print axioms capped_pairing_le_cap_mul_total
#print axioms bounded_column_kernel_pairing

end NSYuDiffuseKernelDecoupling
