import Mathlib

namespace Millennium.RH.WuFloorFiberFalsifier

/-- The floor fiber used in the claimed lower bound:
`J_m = {k : 1 ≤ k ≤ N and floor(N/k) = m}`. -/
def floorFiber (N m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun k => N / k = m)

/-- The numerator of the paper's weight `sum_{k in J_m} k/N`. -/
def fiberNumerator (N m : ℕ) : ℕ :=
  Finset.sum (floorFiber N m) (fun k => k)

/-- After multiplying by the positive denominator `2*m*N`, the claimed
Lemma 9 says `N ≤ 2*m*sum_{k in J_m} k`. -/
def ClaimedLemma9 : Prop :=
  ∀ N m : ℕ, 2 ≤ N → 1 ≤ m →
    N ≤ 2 * m * fiberNumerator N m

/-- BANKER: the universal claim specializes to the in-range pair `N=3,m=2`. -/
theorem banker_claim_specializes_to_three_two (h : ClaimedLemma9) :
    3 ≤ 2 * 2 * fiberNumerator 3 2 := by
  exact h 3 2 (by norm_num) (by norm_num)

/-- CRITIC: `floor(3/k)` takes the values `3,1,1`; hence the `m=2`
fiber is empty, its weight numerator is zero, and the claimed bound fails. -/
theorem critic_three_two_is_an_empty_floor_fiber :
    floorFiber 3 2 = ∅ ∧
      fiberNumerator 3 2 = 0 ∧
      ¬ (3 ≤ 2 * 2 * fiberNumerator 3 2) := by
  have hfiber : floorFiber 3 2 = ∅ := by decide
  simp [hfiber, fiberNumerator]

/-- CLEANER: the all-`m` pointwise lower bound used to derive the RH-sized
mean-square estimate is false. Any repaired lower bound must assume that
`m` is actually attained by `floor(N/k)`. -/
theorem cleaner_claimed_lemma9_is_false : ¬ ClaimedLemma9 := by
  intro h
  exact critic_three_two_is_an_empty_floor_fiber.2.2
    (banker_claim_specializes_to_three_two h)

#print axioms banker_claim_specializes_to_three_two
#print axioms critic_three_two_is_an_empty_floor_fiber
#print axioms cleaner_claimed_lemma9_is_false

end Millennium.RH.WuFloorFiberFalsifier
