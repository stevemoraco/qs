import Mathlib

open scoped BigOperators

namespace PNP
namespace HashFractionalDualFinite

variable {X Seed : Type*} [Fintype X] [Fintype Seed]

def hitWeight
    (weight : X → ℝ)
    (bad : Seed → X → Prop) [∀ s, DecidablePred (bad s)]
    (s : Seed) : ℝ :=
  ∑ x, if bad s x then weight x else 0

def errorProbability
    (mu : Seed → ℝ)
    (bad : Seed → X → Prop) [∀ s, DecidablePred (bad s)]
    (x : X) : ℝ :=
  ∑ s, if bad s x then mu s else 0

theorem weighted_error_fubini
    (mu : Seed → ℝ)
    (weight : X → ℝ)
    (bad : Seed → X → Prop) [∀ s, DecidablePred (bad s)] :
    (∑ s, mu s * hitWeight weight bad s) =
      ∑ x, weight x * errorProbability mu bad x := by
  classical
  simp only [hitWeight, errorProbability]
  calc
    (∑ s, mu s * ∑ x, if bad s x then weight x else 0) =
        ∑ s, ∑ x, if bad s x then mu s * weight x else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          by_cases h : bad s x <;> simp [h]
    _ = ∑ x, ∑ s, if bad s x then mu s * weight x else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ x, weight x * ∑ s, if bad s x then mu s else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          by_cases h : bad s x <;> simp [h, mul_comm]

theorem fractional_transversal_lower
    (mu : Seed → ℝ)
    (weight : X → ℝ)
    (bad : Seed → X → Prop) [∀ s, DecidablePred (bad s)]
    (delta : ℝ)
    (hmu_nonneg : ∀ s, 0 ≤ mu s)
    (hmu_sum : ∑ s, mu s = 1)
    (hweight_nonneg : ∀ x, 0 ≤ weight x)
    (hhit : ∀ s, 1 ≤ hitWeight weight bad s)
    (hpoint : ∀ x, errorProbability mu bad x ≤ delta)
    (hdelta : 0 < delta) :
    1 / delta ≤ ∑ x, weight x := by
  have havgLower : 1 ≤ ∑ s, mu s * hitWeight weight bad s := by
    calc
      1 = ∑ s, mu s := hmu_sum.symm
      _ = ∑ s, mu s * 1 := by simp
      _ ≤ ∑ s, mu s * hitWeight weight bad s := by
        apply Finset.sum_le_sum
        intro s _
        exact mul_le_mul_of_nonneg_left (hhit s) (hmu_nonneg s)
  have hupper :
      (∑ x, weight x * errorProbability mu bad x) ≤
        ∑ x, weight x * delta := by
    apply Finset.sum_le_sum
    intro x _
    exact mul_le_mul_of_nonneg_left (hpoint x) (hweight_nonneg x)
  have hone : 1 ≤ delta * ∑ x, weight x := by
    calc
      1 ≤ ∑ s, mu s * hitWeight weight bad s := havgLower
      _ = ∑ x, weight x * errorProbability mu bad x :=
        weighted_error_fubini mu weight bad
      _ ≤ ∑ x, weight x * delta := hupper
      _ = delta * ∑ x, weight x := by
        rw [Finset.mul_sum]
        simp [mul_comm]
  rw [div_le_iff₀ hdelta]
  simpa [mul_comm] using hone

theorem equality_dnf_gate_identity
    {K ell : ℕ} (hK : 1 ≤ K) (hell : 1 ≤ ell) :
    K * (ell - 1) + (K - 1) = K * ell - 1 := by
  obtain ⟨K', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
  obtain ⟨ell', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ell ≠ 0)
  simp [Nat.mul_succ]

#print axioms weighted_error_fubini
#print axioms fractional_transversal_lower
#print axioms equality_dnf_gate_identity

end HashFractionalDualFinite
end PNP
