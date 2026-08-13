import Mathlib

namespace PNPParityOddSliceRecurrence

/-- The exact two-step coefficient identity behind the parity-walk contraction. -/
theorem coefficient_identity (q : ℝ) :
    (3 * q - 2) + (q - 1) * (q - 2) = q ^ 2 := by
  ring

/-- If the weight-three mass is controlled endpointwise by the weight-one mass,
then the exact two-step parity recurrence contracts.  This is the scalar layer
of the human first-occurrence injection theorem; the injection itself is not
assumed to be formalized here. -/
theorem two_step_contract
    {q p r pnext : ℝ}
    (hq : 3 ≤ q)
    (hinj : 6 * r ≤ (q - 1) * (q - 2) * p)
    (hnext : pnext = ((3 * q - 2) * p + 6 * r) / q ^ 2) :
    pnext ≤ p := by
  have hq2 : 0 < q ^ 2 := by
    nlinarith [sq_nonneg q]
  rw [hnext]
  apply (div_le_iff₀ hq2).2
  nlinarith [hinj, coefficient_identity q]

/-- The direct `k=3` collision probability is at most one for `q>=3`. -/
theorem p3_le_one {q : ℝ} (hq : 3 ≤ q) :
    (3 * q - 2) / q ^ 2 ≤ 1 := by
  have hq2 : 0 < q ^ 2 := by
    nlinarith [sq_nonneg q]
  apply (div_le_iff₀ hq2).2
  nlinarith [sq_nonneg (q - 1)]

/-- One abstract induction step for an odd-slice chain. -/
theorem odd_chain_step
    {P : ℕ → ℝ} {m : ℕ}
    (hcontract : ∀ j, P (j + 2) ≤ P j) :
    P (2 * (m + 1) + 1) ≤ P (2 * m + 1) := by
  convert hcontract (2 * m + 1) using 1 <;> ring

/-- Repeated two-step contraction puts every odd slice after 3 below slice 3. -/
theorem odd_chain_bounded_by_three
    {P : ℕ → ℝ}
    (hcontract : ∀ j, P (j + 2) ≤ P j) :
    ∀ m : ℕ, P (2 * m + 3) ≤ P 3 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hs := hcontract (2 * m + 3)
      have hidx : 2 * (m + 1) + 3 = (2 * m + 3) + 2 := by omega
      rw [hidx]
      exact le_trans hs ih

#print axioms coefficient_identity
#print axioms two_step_contract
#print axioms p3_le_one
#print axioms odd_chain_step
#print axioms odd_chain_bounded_by_three

end PNPParityOddSliceRecurrence
