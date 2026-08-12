import Mathlib

/-!
# P versus NP far-promise finite covering core

HONESTY BOUNDARY

This file formalizes only finite cardinality and logical interfaces:

* a finite union of finite balls has cardinality at most the sum of their
  cardinalities;
* uniform ball capacity bounds the whole cover;
* if covering capacity is strictly below the finite universe, an uncovered
  point exists;
* the abstract contrapositive for one fixed promise problem.

It does not formalize Hamming distance, binary entropy, asymptotics, Boolean
circuits, P-uniformity, P, NP, MCSP, magnification, or the Clay statement.
-/

namespace MillenniumBraid
namespace PNPFarPromiseCoverFinite

open Finset

/-- A finite union of balls, each of cardinality at most `B`, has cardinality
at most `number of centers * B`. -/
theorem finite_ball_cover_card_le
    {ι α : Type*}
    [DecidableEq α]
    (centers : Finset ι)
    (ball : ι → Finset α)
    (B : ℕ)
    (hball : ∀ i ∈ centers, #(ball i) ≤ B) :
    #(centers.biUnion ball) ≤ #centers * B := by
  calc
    #(centers.biUnion ball) ≤ ∑ i ∈ centers, #(ball i) :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ centers, B :=
      Finset.sum_le_sum fun i hi ↦ hball i hi
    _ = #centers * B := by simp

/-- If the total finite covering capacity is strictly smaller than the finite
universe, an uncovered point exists. -/
theorem exists_uncovered_of_cover_capacity_lt
    {ι α : Type*}
    [Fintype α]
    [DecidableEq α]
    (centers : Finset ι)
    (ball : ι → Finset α)
    (B : ℕ)
    (hball : ∀ i ∈ centers, #(ball i) ≤ B)
    (hcap : #centers * B < Fintype.card α) :
    ∃ x : α, x ∉ centers.biUnion ball := by
  classical
  by_contra hnone
  push_neg at hnone
  have hfull : centers.biUnion ball = Finset.univ := by
    ext x
    simp only [mem_biUnion, mem_univ, iff_true]
    exact hnone x
  have hcover := finite_ball_cover_card_le centers ball B hball
  rw [hfull, Finset.card_univ] at hcover
  exact (not_le_of_gt hcap) hcover

/-- Abstract terminality shadow for one fixed promise problem. -/
theorem fixed_far_promise_magnification_contrapositive
    (PEqualsNP SmallUniformCircuits : Prop)
    (hcollapse : PEqualsNP → SmallUniformCircuits)
    (hlower : ¬ SmallUniformCircuits) :
    ¬ PEqualsNP := by
  intro heq
  exact hlower (hcollapse heq)

#print axioms finite_ball_cover_card_le
#print axioms exists_uncovered_of_cover_capacity_lt
#print axioms fixed_far_promise_magnification_contrapositive

end PNPFarPromiseCoverFinite
end MillenniumBraid
