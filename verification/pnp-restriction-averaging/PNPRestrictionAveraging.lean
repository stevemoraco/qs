import Mathlib

open scoped BigOperators

namespace PNP.RestrictionAveraging

variable {R X : Type*} [Fintype R] [Fintype X]

def globalWeight (μ : R → ℝ) (ν : R → X → ℝ) (x : X) : ℝ :=
  ∑ r, μ r * ν r x

theorem globalWeight_nonneg
    (μ : R → ℝ) (ν : R → X → ℝ)
    (hμ : ∀ r, 0 ≤ μ r)
    (hν : ∀ r x, 0 ≤ ν r x) :
    ∀ x, 0 ≤ globalWeight μ ν x := by
  intro x
  exact Finset.sum_nonneg (fun r _ => mul_nonneg (hμ r) (hν r x))

theorem globalWeight_sum_one
    (μ : R → ℝ) (ν : R → X → ℝ)
    (hμ : ∑ r, μ r = 1)
    (hν : ∀ r, ∑ x, ν r x = 1) :
    ∑ x, globalWeight μ ν x = 1 := by
  calc
    ∑ x, globalWeight μ ν x
        = ∑ r, μ r * ∑ x, ν r x := by
          simp only [globalWeight]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.mul_sum]
    _ = ∑ r, μ r := by
          apply Finset.sum_congr rfl
          intro r _
          rw [hν r, mul_one]
    _ = 1 := hμ

theorem global_error_fubini
    (μ : R → ℝ) (ν : R → X → ℝ) (err : X → ℝ) :
    ∑ x, globalWeight μ ν x * err x
      = ∑ r, μ r * ∑ x, ν r x * err x := by
  simp only [globalWeight]
  calc
    ∑ x, (∑ r, μ r * ν r x) * err x
        = ∑ x, ∑ r, (μ r * ν r x) * err x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
    _ = ∑ r, ∑ x, (μ r * ν r x) * err x := by
          rw [Finset.sum_comm]
    _ = ∑ r, μ r * ∑ x, ν r x * err x := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring

theorem local_to_global_error_floor
    (μ : R → ℝ) (ν : R → X → ℝ) (err : X → ℝ)
    (good : R → Prop) [DecidablePred good]
    (ρ η : ℝ)
    (hη : 0 ≤ η)
    (hμ : ∀ r, 0 ≤ μ r)
    (hν : ∀ r x, 0 ≤ ν r x)
    (herr : ∀ x, 0 ≤ err x)
    (hgoodMass : ρ ≤ ∑ r with good r, μ r)
    (hlocal : ∀ r, good r → η ≤ ∑ x, ν r x * err x) :
    ρ * η ≤ ∑ x, globalWeight μ ν x * err x := by
  let localError : R → ℝ := fun r => ∑ x, ν r x * err x
  have hlocalNonneg : ∀ r, 0 ≤ localError r := by
    intro r
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hν r x) (herr x))
  have hterm : ∀ r,
      (if good r then μ r * η else 0) ≤ μ r * localError r := by
    intro r
    by_cases hr : good r
    · simp only [hr, if_true]
      exact mul_le_mul_of_nonneg_left (hlocal r hr) (hμ r)
    · simp only [hr, if_false]
      exact mul_nonneg (hμ r) (hlocalNonneg r)
  have hsum :
      (∑ r with good r, μ r) * η ≤ ∑ r, μ r * localError r := by
    calc
      (∑ r with good r, μ r) * η
          = ∑ r, if good r then μ r * η else 0 := by
              classical
              rw [Finset.filter_sum]
              rw [Finset.sum_mul]
      _ ≤ ∑ r, μ r * localError r :=
          Finset.sum_le_sum (fun r _ => hterm r)
  calc
    ρ * η ≤ (∑ r with good r, μ r) * η :=
      mul_le_mul_of_nonneg_right hgoodMass hη
    _ ≤ ∑ r, μ r * localError r := hsum
    _ = ∑ x, globalWeight μ ν x * err x := by
      symm
      exact global_error_fubini μ ν err

theorem expectation_le_pointwise
    (w : X → ℝ) (err : X → ℝ) (ε δ : ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hsum : ∑ x, w x = 1)
    (hpoint : ∀ x, err x ≤ ε)
    (havg : δ ≤ ∑ x, w x * err x) :
    δ ≤ ε := by
  calc
    δ ≤ ∑ x, w x * err x := havg
    _ ≤ ∑ x, w x * ε := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (hpoint x) (hw x)
    _ = (∑ x, w x) * ε := by rw [Finset.sum_mul]
    _ = ε := by rw [hsum, one_mul]

theorem no_pointwise_error_below_local_floor
    (w : X → ℝ) (err : X → ℝ) (ε ρ η : ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hsum : ∑ x, w x = 1)
    (hpoint : ∀ x, err x ≤ ε)
    (havg : ρ * η ≤ ∑ x, w x * err x)
    (hstrict : ε < ρ * η) : False := by
  have h := expectation_le_pointwise w err ε (ρ * η) hw hsum hpoint havg
  linarith

theorem eleven_slot_error_floor
    {ρ globalError : ℝ}
    (hlocalGlobal : ρ / 11 ≤ globalError) :
    ρ * (1 / 11 : ℝ) ≤ globalError := by
  norm_num at *
  linarith

#print axioms globalWeight_nonneg
#print axioms globalWeight_sum_one
#print axioms global_error_fubini
#print axioms local_to_global_error_floor
#print axioms expectation_le_pointwise
#print axioms no_pointwise_error_below_local_floor
#print axioms eleven_slot_error_floor

end PNP.RestrictionAveraging
