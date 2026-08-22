import Mathlib

namespace PNPMcspUniformityAudit

/-- A two-threshold promise witness: the low threshold requires rejection,
while the high threshold requires acceptance. -/
inductive ThresholdChoice
  | low
  | high
  deriving DecidableEq, Fintype

/-- Required answer on a witness that is a NO instance at the low threshold
and a YES instance at the high threshold. -/
def requiredAnswer : ThresholdChoice → Bool
  | ThresholdChoice.low => false
  | ThresholdChoice.high => true

/-- No single Boolean answer is correct for both incompatible threshold
choices. -/
theorem one_answer_cannot_decide_both (answer : Bool) :
    answer ≠ requiredAnswer ThresholdChoice.low ∨
      answer ≠ requiredAnswer ThresholdChoice.high := by
  cases answer <;> simp [requiredAnswer]

/-- Diagonal threshold choice against an enumerated family of Boolean
answers. At index `i`, choose the threshold whose required answer is the
opposite of the `i`-th candidate's answer at its assigned index. -/
def diagonalThreshold (candidate : ℕ → ℕ → Bool) (i : ℕ) : ThresholdChoice :=
  if candidate i i then ThresholdChoice.low else ThresholdChoice.high

/-- Every enumerated candidate fails at its own diagonal index. -/
theorem diagonal_threshold_defeats
    (candidate : ℕ → ℕ → Bool) (i : ℕ) :
    candidate i i ≠ requiredAnswer (diagonalThreshold candidate i) := by
  cases h : candidate i i <;>
    simp [diagonalThreshold, requiredAnswer, h]

/-- The raw diagonal bit sequence, useful when the two thresholds are
encoded by `false` and `true`. -/
def diagonalBits (candidate : ℕ → ℕ → Bool) : ℕ → Bool :=
  fun i => !(candidate i i)

/-- The diagonal bit differs from every candidate on its assigned index. -/
theorem diagonal_bits_disagree
    (candidate : ℕ → ℕ → Bool) (i : ℕ) :
    diagonalBits candidate i ≠ candidate i i := by
  cases h : candidate i i <;> simp [diagonalBits, h]

/-- Numeric encoding of the two threshold choices. -/
def thresholdValue (low high : ℕ) : ThresholdChoice → ℕ
  | ThresholdChoice.low => low
  | ThresholdChoice.high => high

/-- If both endpoint thresholds obey a common upper bound, every diagonal
choice obeys it as well. -/
theorem diagonal_threshold_bounded
    {low high bound : ℕ}
    (hLow : low ≤ bound) (hHigh : high ≤ bound)
    (candidate : ℕ → ℕ → Bool) (i : ℕ) :
    thresholdValue low high (diagonalThreshold candidate i) ≤ bound := by
  unfold diagonalThreshold
  split <;> simp [thresholdValue, hLow, hHigh]

#print axioms one_answer_cannot_decide_both
#print axioms diagonal_threshold_defeats
#print axioms diagonal_bits_disagree
#print axioms diagonal_threshold_bounded

end PNPMcspUniformityAudit
