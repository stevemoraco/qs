import Mathlib

open Finset

namespace B5BSDSmithFamily

/-- Abstract finite-level length of one Smith summand of depth `a`. -/
def truncLength (a k : ℕ) : ℕ := if a < k then a else k

/-- The adjacent-level jump of a single Smith summand is exactly one iff its
Smith depth reaches the new level. -/
theorem truncLength_step (a p : ℕ) (hp : 0 < p) :
    truncLength a p = truncLength a (p - 1) + (if p ≤ a then 1 else 0) := by
  unfold truncLength
  by_cases hpa : p ≤ a
  · have hnot : ¬ a < p := by omega
    have hnotprev : ¬ a < p - 1 := by omega
    simp [hpa, hnot, hnotprev]
    omega
  · have hap : a < p := by omega
    by_cases haprev : a < p - 1
    · simp [hpa, hap, haprev]
    · have heq : a = p - 1 := by omega
      simp [hpa, hap, haprev, heq]

#print axioms truncLength_step

/-- For a finite indexed family of Smith summands, the adjacent finite-level
length jump is exactly the number of summands whose depth reaches level `p`. -/
theorem smith_family_jump
    {I : Type*} [DecidableEq I]
    (s : Finset I) (depth : I → ℕ) (p : ℕ) (hp : 0 < p) :
    (∑ i ∈ s, truncLength (depth i) p) =
      (∑ i ∈ s, truncLength (depth i) (p - 1)) +
        #(s.filter fun i ↦ p ≤ depth i) := by
  calc
    (∑ i ∈ s, truncLength (depth i) p) =
        ∑ i ∈ s, (truncLength (depth i) (p - 1) +
          (if p ≤ depth i then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact truncLength_step (depth i) p hp
    _ = (∑ i ∈ s, truncLength (depth i) (p - 1)) +
        ∑ i ∈ s, (if p ≤ depth i then 1 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i ∈ s, truncLength (depth i) (p - 1)) +
        #(s.filter fun i ↦ p ≤ depth i) := by
          congr 1
          simp

#print axioms smith_family_jump

end B5BSDSmithFamily
