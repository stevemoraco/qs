import Mathlib

/-!
# P versus NP linear random-list finite arithmetic

This file verifies only scalar inequalities used in the random quad-list
covering and CLY padding ledger.  It does not formalize circuits, probability,
the probabilistic method, sparse languages, Chen--Li--Yang, NP, or `P != NP`.
-/

namespace MillenniumBraid
namespace PNPLinearRandomListFinite

theorem acceptedFractionAtMostInvSquare
    (n Q : ℚ)
    (hn : 2304 ≤ n)
    (hQ : n ^ 4 / 192 ≤ Q) :
    12 * n / Q ≤ 1 / n ^ 2 := by
  have hnpos : 0 < n := by linarith
  have hnnonneg : 0 ≤ n := le_of_lt hnpos
  have hbase : 0 < n ^ 4 / 192 := by positivity
  have hQpos : 0 < Q := lt_of_lt_of_le hbase hQ
  have hmul : 2304 * n ^ 3 ≤ n * n ^ 3 := by
    exact mul_le_mul_of_nonneg_right hn (pow_nonneg hnnonneg 3)
  have hscale : 12 * n ^ 3 ≤ n ^ 4 / 192 := by
    calc
      12 * n ^ 3 = (2304 * n ^ 3) / 192 := by ring
      _ ≤ (n * n ^ 3) / 192 :=
        div_le_div_of_nonneg_right hmul (by norm_num)
      _ = n ^ 4 / 192 := by ring
  have htarget : 12 * n * n ^ 2 ≤ Q := by
    calc
      12 * n * n ^ 2 = 12 * n ^ 3 := by ring
      _ ≤ n ^ 4 / 192 := hscale
      _ ≤ Q := hQ
  apply (div_le_div_iff₀ hQpos (pow_pos hnpos 2)).2
  simpa using htarget

theorem falsePositiveFloor
    (n Q : ℚ)
    (hn : 0 < n)
    (hQpos : 0 < Q)
    (hQ : Q ≤ n ^ 4 / 24) :
    144 / n ^ 3 ≤ (6 * n) / Q := by
  apply (div_le_div_iff₀ (pow_pos hn 3) hQpos).2
  have hmul : 144 * Q ≤ 144 * (n ^ 4 / 24) :=
    mul_le_mul_of_nonneg_left hQ (by norm_num)
  nlinarith

theorem unionBoundExponentHeadroom
    (n L : ℚ) (hn : 0 < n) (hL : 0 < L) :
    10 * n * L < 12 * n * L := by
  have hprod : 0 < n * L := mul_pos hn hL
  nlinarith

theorem linearListExceedsSquareRootBudget
    (x : ℚ) (hx : 1 ≤ x) :
    x < 6 * x ^ 2 := by
  nlinarith [sq_nonneg (x - 1)]

theorem clyExponentFactorTwo
    (c q : ℚ) (hc : 0 < c) (hq : 0 < q) :
    c * q < 2 * c * q := by
  have hprod : 0 < c * q := mul_pos hc hq
  nlinarith

theorem selectedToFalsePositiveLedger
    (accepted selected M : ℕ)
    (haccepted : 2 * M < accepted)
    (hselected : selected ≤ M) :
    M < accepted - selected := by
  omega

#print axioms acceptedFractionAtMostInvSquare
#print axioms falsePositiveFloor
#print axioms unionBoundExponentHeadroom
#print axioms linearListExceedsSquareRootBudget
#print axioms clyExponentFactorTwo
#print axioms selectedToFalsePositiveLedger

end PNPLinearRandomListFinite
end MillenniumBraid
