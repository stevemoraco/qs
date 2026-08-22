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

/-- Restricting an `r`-bit selector prefix does not increase gates, so a
`2(m+r)+S` gate upper bound becomes surplus `S+2r` against baseline `2m`.
The graph-theoretic restriction step itself is outside this scalar lemma. -/
theorem sliceRestrictionBudget
    (m r S g : ℕ)
    (h : g ≤ 2 * (m + r) + S) :
    g ≤ 2 * m + (S + 2 * r) := by
  omega

/-- If a fixed core has size `M` and an error edge contains `e` core points
with `M ≤ 4e`, uniform fractional core weight gives that edge mass at least 1. -/
theorem quarterCoreEdgeMass
    (M e : ℚ)
    (hM : 0 < M)
    (he : M ≤ 4 * e) :
    1 ≤ (4 * e) / M := by
  exact (le_div_iff₀ hM).2 (by simpa using he)

/-- Uniform weight `4/M` over `M` core points has total mass exactly four. -/
theorem quarterCoreTotalMass
    (M : ℚ)
    (hM : 0 < M) :
    (4 * M) / M = 4 := by
  field_simp [ne_of_gt hM]

/-- The chosen sample size `256*n*L` has an exact integral quarter. -/
theorem sampleQuarterScaled
    (n L : ℕ) :
    256 * n * L = 4 * (64 * n * L) := by
  ring

#print axioms acceptedFractionAtMostInvSquare
#print axioms falsePositiveFloor
#print axioms unionBoundExponentHeadroom
#print axioms linearListExceedsSquareRootBudget
#print axioms clyExponentFactorTwo
#print axioms selectedToFalsePositiveLedger
#print axioms sliceRestrictionBudget
#print axioms quarterCoreEdgeMass
#print axioms quarterCoreTotalMass
#print axioms sampleQuarterScaled

end PNPLinearRandomListFinite
end MillenniumBraid
