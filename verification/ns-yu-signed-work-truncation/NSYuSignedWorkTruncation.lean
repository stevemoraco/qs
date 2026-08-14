import Mathlib

/-!
# Signed Yu work truncation firewall

Finite weighted real algebra only. For a signed work density `c i * k i` with
`|k i| ≤ M`, discarding a tail of total variation `T_tail` can remove at most
`M * T_tail` positive work. Hence a normalized work margin survives any
truncation whose total-variation tail is sufficiently small.

This file does **not** formalize Yu's PDE work density, uniform integrability,
tightness, Young measures, recurrence, Navier--Stokes regularity, or blow-up.
-/

open scoped BigOperators

noncomputable section

namespace NSYuSignedWorkTruncation

variable {ι : Type*} [Fintype ι]

/-- Work retained by a decidable truncation predicate. -/
def retainedWork (keep : ι → Prop) [DecidablePred keep]
    (c k : ι → ℝ) : ℝ :=
  ∑ i, if keep i then c i * k i else 0

/-- Work discarded by the truncation. -/
def tailWork (keep : ι → Prop) [DecidablePred keep]
    (c k : ι → ℝ) : ℝ :=
  ∑ i, if keep i then 0 else c i * k i

/-- Total variation retained by the truncation. -/
def retainedTV (keep : ι → Prop) [DecidablePred keep]
    (c : ι → ℝ) : ℝ :=
  ∑ i, if keep i then |c i| else 0

/-- Total variation discarded by the truncation. -/
def tailTV (keep : ι → Prop) [DecidablePred keep]
    (c : ι → ℝ) : ℝ :=
  ∑ i, if keep i then 0 else |c i|

/-- Exact decomposition of total work into retained and discarded parts. -/
theorem work_split (keep : ι → Prop) [DecidablePred keep]
    (c k : ι → ℝ) :
    (∑ i, c i * k i) = retainedWork keep c k + tailWork keep c k := by
  unfold retainedWork tailWork
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : keep i <;> simp [hi]

/-- Exact decomposition of total variation. -/
theorem totalVariation_split (keep : ι → Prop) [DecidablePred keep]
    (c : ι → ℝ) :
    (∑ i, |c i|) = retainedTV keep c + tailTV keep c := by
  unfold retainedTV tailTV
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : keep i <;> simp [hi]

/-- Discarded signed work is bounded above by `M` times discarded total
variation. This is the exact direction needed to lower-bound retained work. -/
theorem tailWork_le_totalVariation
    (keep : ι → Prop) [DecidablePred keep]
    (c k : ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hk : ∀ i, |k i| ≤ M) :
    tailWork keep c k ≤ M * tailTV keep c := by
  unfold tailWork tailTV
  calc
    (∑ i, if keep i then 0 else c i * k i) ≤
        ∑ i, if keep i then 0 else |c i| * M := by
      apply Finset.sum_le_sum
      intro i _hi
      by_cases hi : keep i
      · simp [hi]
      · simp only [hi, if_false]
        calc
          c i * k i ≤ |c i * k i| := le_abs_self _
          _ = |c i| * |k i| := abs_mul _ _
          _ ≤ |c i| * M :=
            mul_le_mul_of_nonneg_left (hk i) (abs_nonneg _)
    _ = M * (∑ i, if keep i then 0 else |c i|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hi : keep i <;> simp [hi, mul_comm]

/-- Retained total variation never exceeds total variation. -/
theorem retainedTV_le_totalVariation
    (keep : ι → Prop) [DecidablePred keep]
    (c : ι → ℝ) :
    retainedTV keep c ≤ ∑ i, |c i| := by
  unfold retainedTV
  apply Finset.sum_le_sum
  intro i _hi
  by_cases hi : keep i
  · simp [hi]
  · simp [hi, abs_nonneg]

/-- A total work floor survives a tail budget, losing exactly `M * δ` in the
normalized margin. -/
theorem retainedWork_margin
    (keep : ι → Prop) [DecidablePred keep]
    (c k : ι → ℝ) (α M δ : ℝ)
    (hM : 0 ≤ M)
    (hk : ∀ i, |k i| ≤ M)
    (hmean : α * (∑ i, |c i|) ≤ ∑ i, c i * k i)
    (htail : tailTV keep c ≤ δ * (∑ i, |c i|)) :
    (α - M * δ) * (∑ i, |c i|) ≤ retainedWork keep c k := by
  have htailWork := tailWork_le_totalVariation keep c k M hM hk
  have htailScaled :
      M * tailTV keep c ≤ M * (δ * (∑ i, |c i|)) :=
    mul_le_mul_of_nonneg_left htail hM
  have hsplit := work_split keep c k
  calc
    (α - M * δ) * (∑ i, |c i|) =
        α * (∑ i, |c i|) - M * (δ * (∑ i, |c i|)) := by ring
    _ ≤ (∑ i, c i * k i) - M * (δ * (∑ i, |c i|)) := by
      exact sub_le_sub_right hmean _
    _ ≤ (∑ i, c i * k i) - tailWork keep c k := by
      linarith
    _ = retainedWork keep c k := by
      linarith

/-- If the surviving margin and total variation are positive, the retained work
is strictly positive. -/
theorem positive_margin_gives_positive_retainedWork
    (keep : ι → Prop) [DecidablePred keep]
    (c k : ι → ℝ) (α M δ : ℝ)
    (hM : 0 ≤ M)
    (hk : ∀ i, |k i| ≤ M)
    (hmargin : 0 < α - M * δ)
    (htv : 0 < ∑ i, |c i|)
    (hmean : α * (∑ i, |c i|) ≤ ∑ i, c i * k i)
    (htail : tailTV keep c ≤ δ * (∑ i, |c i|)) :
    0 < retainedWork keep c k := by
  have hfloor := retainedWork_margin keep c k α M δ hM hk hmean htail
  have hpositive : 0 < (α - M * δ) * (∑ i, |c i|) :=
    mul_pos hmargin htv
  linarith

/-- The surviving margin also holds relative to the smaller retained total
variation whenever it is nonnegative. -/
theorem retained_relative_margin
    (keep : ι → Prop) [DecidablePred keep]
    (c k : ι → ℝ) (α M δ : ℝ)
    (hM : 0 ≤ M)
    (hk : ∀ i, |k i| ≤ M)
    (hmargin : 0 ≤ α - M * δ)
    (hmean : α * (∑ i, |c i|) ≤ ∑ i, c i * k i)
    (htail : tailTV keep c ≤ δ * (∑ i, |c i|)) :
    (α - M * δ) * retainedTV keep c ≤ retainedWork keep c k := by
  have htvle := retainedTV_le_totalVariation keep c
  have hscaled :
      (α - M * δ) * retainedTV keep c ≤
        (α - M * δ) * (∑ i, |c i|) :=
    mul_le_mul_of_nonneg_left htvle hmargin
  exact hscaled.trans
    (retainedWork_margin keep c k α M δ hM hk hmean htail)

/-- The coefficient `M` is sharp already for one discarded atom whose
observable equals the upper bound. -/
theorem one_atom_tail_loss_is_sharp (c M : ℝ) (hc : 0 ≤ c) :
    c * M = M * |c| := by
  rw [abs_of_nonneg hc, mul_comm]

#print axioms retainedWork
#print axioms tailWork
#print axioms retainedTV
#print axioms tailTV
#print axioms work_split
#print axioms totalVariation_split
#print axioms tailWork_le_totalVariation
#print axioms retainedTV_le_totalVariation
#print axioms retainedWork_margin
#print axioms positive_margin_gives_positive_retainedWork
#print axioms retained_relative_margin
#print axioms one_atom_tail_loss_is_sharp

end NSYuSignedWorkTruncation
