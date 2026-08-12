import Mathlib

/-!
# P versus NP random-selector incidence ledger

Honesty status: this file formalizes only exact finite arithmetic used in the
random marker-selector covering theorem.  It does not formalize Boolean
circuits, random selectors, AM--GM, the probabilistic method, Chen--Li--Yang,
NP, or `P != NP`.
-/

namespace MillenniumBraid
namespace PNPRandomSelectorIncidenceLedger

def pairCount (n : ℚ) : ℚ := n * (n - 1) / 2

def completionCount (n : ℚ) : ℚ := (n - 2) * (n - 3) / 2

def fourSetCount (n : ℚ) : ℚ :=
  n * (n - 1) * (n - 2) * (n - 3) / 24

theorem sixIncidenceCountIdentity (n : ℚ) :
    pairCount n * completionCount n = 6 * fourSetCount n := by
  simp [pairCount, completionCount, fourSetCount]
  ring

theorem pairCountAtMostQuarterFourSetCount
    (n : ℚ) (hn : 10 ≤ n) :
    pairCount n ≤ fourSetCount n / 4 := by
  have hnonneg : 0 ≤ n * (n - 1) := by
    positivity
  have hprod : 48 ≤ (n - 2) * (n - 3) := by
    nlinarith [sq_nonneg (n - 10)]
  have hmul := mul_le_mul_of_nonneg_left hprod hnonneg
  simp [pairCount, fourSetCount]
  nlinarith

theorem twoThirdsNegativeAcceptanceLedger
    (W S A : ℚ)
    (hW : 0 < W)
    (hS0 : 0 ≤ S)
    (hS : S ≤ W / 4)
    (hA : 3 * W / 4 ≤ A) :
    (2 / 3 : ℚ) * (W - S) ≤ A - S := by
  nlinarith

theorem conservativeExponentHeadroom :
    (3 / 64 : ℚ) < 2 / 15 := by
  norm_num

theorem nearLinearSelectorRejectionScale
    (A n : ℝ) (hn : 0 < n) :
    n ^ 2 * (A * Real.log n / n) = A * n * Real.log n := by
  field_simp
  ring

theorem deterministicFloorSurvivesConvexMixing
    (weights errors e : Finset ℕ -> ℝ)
    (S : Finset (Finset ℕ))
    (hweights : ∑ s ∈ S, weights s = 1)
    (hweightNonneg : ∀ s ∈ S, 0 ≤ weights s)
    (hfloor : ∀ s ∈ S, e ≤ errors s) :
    e ≤ ∑ s ∈ S, weights s * errors s := by
  calc
    e = ∑ s ∈ S, weights s * e := by
      rw [← Finset.sum_mul]
      rw [hweights]
      simp
    _ ≤ ∑ s ∈ S, weights s * errors s := by
      gcongr with s hs
      exact hfloor s hs

#print axioms sixIncidenceCountIdentity
#print axioms pairCountAtMostQuarterFourSetCount
#print axioms twoThirdsNegativeAcceptanceLedger
#print axioms conservativeExponentHeadroom
#print axioms nearLinearSelectorRejectionScale
#print axioms deterministicFloorSurvivesConvexMixing

end PNPRandomSelectorIncidenceLedger
end MillenniumBraid
