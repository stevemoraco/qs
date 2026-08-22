import Mathlib

/-!
# P versus NP: finite exact hard-core threshold logic

This file formalizes only the source-independent quantifier step used in the
dense-support entropy obstruction.  If a finite test set defeats every
candidate of cost at most `S`, but one candidate of cost at most `B` agrees
with the target everywhere on the test set, then necessarily `S < B`.

It does not formalize Viola's 2026 circuit upper bound, Boolean circuits,
entropy, asymptotics, or `P != NP`.
-/

namespace PNP
namespace DenseHardCoreFinite

/-- A candidate agrees with the target at every point of a finite test set. -/
def AgreesOn {X Y : Type*}
    (T : Finset X) (target candidate : X → Y) : Prop :=
  ∀ x ∈ T, candidate x = target x

/--
`T` is an exact test set against every candidate whose declared cost is at
most `S`.
-/
def ExactTestSetUpTo {X Y Candidate : Type*}
    (T : Finset X) (target : X → Y)
    (eval : Candidate → X → Y) (cost : Candidate → ℕ)
    (S : ℕ) : Prop :=
  ∀ candidate, cost candidate ≤ S →
    ¬ AgreesOn T target (eval candidate)

/-- A genuinely small perfect agreer contradicts exact hardness directly. -/
theorem no_exact_test_set_if_small_agreer
    {X Y Candidate : Type*}
    (T : Finset X) (target : X → Y)
    (eval : Candidate → X → Y) (cost : Candidate → ℕ)
    (S : ℕ)
    (hard : ExactTestSetUpTo T target eval cost S)
    (candidate : Candidate)
    (hcost : cost candidate ≤ S)
    (hagrees : AgreesOn T target (eval candidate)) :
    False := by
  exact (hard candidate hcost) hagrees

/--
If a perfect agreer exists below an upper threshold `B`, an exact test set
can only certify hardness strictly below `B`.
-/
theorem certified_threshold_lt_upper_bound
    {X Y Candidate : Type*}
    (T : Finset X) (target : X → Y)
    (eval : Candidate → X → Y) (cost : Candidate → ℕ)
    (S B : ℕ)
    (hard : ExactTestSetUpTo T target eval cost S)
    (candidate : Candidate)
    (hcost : cost candidate ≤ B)
    (hagrees : AgreesOn T target (eval candidate)) :
    S < B := by
  by_contra hnot
  have hBS : B ≤ S := Nat.le_of_not_gt hnot
  exact no_exact_test_set_if_small_agreer
    T target eval cost S hard candidate (hcost.trans hBS) hagrees

/-- The same finite implication with an exponential upper threshold. -/
theorem certified_threshold_lt_two_pow
    {X Y Candidate : Type*}
    (T : Finset X) (target : X → Y)
    (eval : Candidate → X → Y) (cost : Candidate → ℕ)
    (S exponent : ℕ)
    (hard : ExactTestSetUpTo T target eval cost S)
    (candidate : Candidate)
    (hcost : cost candidate ≤ 2 ^ exponent)
    (hagrees : AgreesOn T target (eval candidate)) :
    S < 2 ^ exponent := by
  exact certified_threshold_lt_upper_bound
    T target eval cost S (2 ^ exponent) hard candidate hcost hagrees

/-- Perfect agreement means the finite error set is empty. -/
theorem error_finset_eq_empty_of_agreesOn
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (T : Finset X) (target candidate : X → Y)
    (hagrees : AgreesOn T target candidate) :
    T.filter (fun x => candidate x ≠ target x) = ∅ := by
  ext x
  simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false, not_and]
  intro hx
  exact not_ne_iff.mpr (hagrees x hx)

/-- Hence a perfect agreer has zero errors on the finite support. -/
theorem error_card_eq_zero_of_agreesOn
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (T : Finset X) (target candidate : X → Y)
    (hagrees : AgreesOn T target candidate) :
    (T.filter (fun x => candidate x ≠ target x)).card = 0 := by
  rw [error_finset_eq_empty_of_agreesOn T target candidate hagrees]
  rfl

#print axioms no_exact_test_set_if_small_agreer
#print axioms certified_threshold_lt_upper_bound
#print axioms certified_threshold_lt_two_pow
#print axioms error_finset_eq_empty_of_agreesOn
#print axioms error_card_eq_zero_of_agreesOn

end DenseHardCoreFinite
end PNP
