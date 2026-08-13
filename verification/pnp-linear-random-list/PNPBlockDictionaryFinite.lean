import Mathlib

/-!
# Finite scalar core for the PNP block-dictionary compiler

This file formalizes the finite averaging, two-level slot accounting, exact
`2N` OR-tree ledger, and the four semantic output cases used by the compiler
obstruction.

It does NOT formalize GF(2) matrices, the Lupanov lookup construction,
fan-in-two circuit syntax, asymptotic estimates, Chen--Li--Yang magnification,
or P versus NP. Those interfaces remain human-audited hypotheses.
-/

namespace MillenniumBraid
namespace PNPBlockDictionaryFinite

/-- A strict average bound over a nonempty finite family has a witness below
the threshold. This is the finite selection step used for the first hash. -/
theorem exists_lt_of_sum_lt_card_mul
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℚ) (B : ℚ)
    (h : (∑ i, f i) < (Fintype.card ι : ℚ) * B) :
    ∃ i, f i < B := by
  by_contra hNo
  push_neg at hNo
  have hSum : (∑ _i : ι, B) ≤ ∑ i, f i := by
    exact Finset.sum_le_sum (fun i _hi => hNo i)
  have hConst : (∑ _i : ι, B) = (Fintype.card ι : ℚ) * B := by
    simp
  rw [hConst] at hSum
  linarith

/-- If the total of nonnegative integer collision counts is smaller than the
number of hash choices, some choice has zero collisions. -/
theorem exists_zero_of_sum_lt_card
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (collisions : ι → ℕ)
    (h : (∑ i, collisions i) < Fintype.card ι) :
    ∃ i, collisions i = 0 := by
  by_contra hNo
  push_neg at hNo
  have hPoint : ∀ i, 1 ≤ collisions i := by
    intro i
    exact Nat.one_le_iff_ne_zero.mpr (hNo i)
  have hSum : (∑ _i : ι, 1) ≤ ∑ i, collisions i := by
    exact Finset.sum_le_sum (fun i _hi => hPoint i)
  have hConst : (∑ _i : ι, 1) = Fintype.card ι := by
    simp
  rw [hConst] at hSum
  omega

/-- With `M ≤ B`, the expected first-level sum of squared bucket sizes
`M + M(M-1)/B` is strictly below `2M`. -/
theorem firstLevelExpectationLtTwoM
    (M B : ℚ)
    (hM : 1 ≤ M)
    (hB : M ≤ B) :
    M + M * (M - 1) / B < 2 * M := by
  have hBPos : 0 < B := lt_of_lt_of_le (by norm_num) (hM.trans hB)
  have hNonneg : 0 ≤ M - 1 := sub_nonneg.mpr hM
  have hMul : M * (M - 1) ≤ (M - 1) * B := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hB hNonneg
  have hDiv : M * (M - 1) / B ≤ M - 1 := by
    apply (div_le_iff₀ hBPos).2
    exact hMul
  linarith

/-- A second table of size at least `r^2` makes the expected number of
colliding unordered pairs strictly less than one. -/
theorem secondLevelExpectedPairsLtOne
    (r tableSize : ℚ)
    (hr : 1 ≤ r)
    (hTable : r * r ≤ tableSize) :
    (r * (r - 1) / 2) / tableSize < 1 := by
  have hrPos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hSquarePos : 0 < r * r := mul_pos hrPos hrPos
  have hTablePos : 0 < tableSize := hSquarePos.trans_le hTable
  apply (div_lt_iff₀ hTablePos).2
  have hNumerator : r * (r - 1) / 2 < r * r := by
    nlinarith
  exact hNumerator.trans_le hTable

/-- If the first-level squared bucket sum is below `2M` and second-level
allocation is at most twice that sum, total table space is below `4M`. -/
theorem secondLevelSlotsLtFourM
    (M sumSquares slots : ℚ)
    (hSquares : sumSquares < 2 * M)
    (hSlots : slots ≤ 2 * sumSquares) :
    slots < 4 * M := by
  linarith

/-- The two shared OR forests have exact cost `(N-k)+(N-b)`, i.e. the `2N`
baseline minus one gate per block and one gate per local coordinate. -/
theorem twoOrForestsBaseIdentity (N k b : ℤ) :
    (N - k) + (N - b) = 2 * N - k - b := by
  ring

/-- Scalar firewall for adding all other compiler gates to the two OR
forests. -/
theorem compilerWithinFrontier
    (N k b extra frontier : ℚ)
    (hExtra : extra - k - b ≤ frontier) :
    (N - k) + (N - b) + extra ≤ 2 * N + frontier := by
  linarith

/-- Semantic output of the compiler. The relation decoder is consulted only
on the exact-one-block, exact-local-weight branch. -/
def compilerOutput
    (allOccupied oneBlock weightOne weightFixed relation : Bool) : Bool :=
  allOccupied ||
    (oneBlock && (weightOne || (weightFixed && relation)))

@[simp] theorem acceptsAllOccupied
    (oneBlock weightOne weightFixed relation : Bool) :
    compilerOutput true oneBlock weightOne weightFixed relation = true := by
  simp [compilerOutput]

@[simp] theorem acceptsSingleton :
    compilerOutput false true true false false = true := by
  decide

@[simp] theorem acceptsStoredFixedWeight :
    compilerOutput false true false true true = true := by
  decide

@[simp] theorem rejectsUnstoredFixedWeight :
    compilerOutput false true false true false = false := by
  decide

#print axioms exists_lt_of_sum_lt_card_mul
#print axioms exists_zero_of_sum_lt_card
#print axioms firstLevelExpectationLtTwoM
#print axioms secondLevelExpectedPairsLtOne
#print axioms secondLevelSlotsLtFourM
#print axioms twoOrForestsBaseIdentity
#print axioms compilerWithinFrontier
#print axioms acceptsAllOccupied
#print axioms acceptsSingleton
#print axioms acceptsStoredFixedWeight
#print axioms rejectsUnstoredFixedWeight

end PNPBlockDictionaryFinite
end MillenniumBraid
