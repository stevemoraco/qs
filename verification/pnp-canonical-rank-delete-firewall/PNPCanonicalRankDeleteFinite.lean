import Mathlib

namespace PNPCanonicalRankDeleteFinite

/-- Consecutive bad ranks give nondecreasing deletion thresholds.
    Integer indices avoid truncated natural subtraction. -/
theorem shifted_threshold_step
    (beta_i beta_next i : ℤ)
    (hstep : beta_i + 1 ≤ beta_next) :
    beta_i - i ≤ beta_next - (i + 1) := by
  linarith

/-- Arithmetic core of the deletion-rank formula.  If exactly the first `q`
    deletion thresholds lie at or below `j`, then their bad ranks are below
    `j+q`, while the next bad rank is above `j+q`. -/
theorem rank_delete_window
    (beta : ℤ → ℤ) (j q : ℤ)
    (hleft : ∀ i : ℤ, 0 ≤ i → i < q → beta i - i ≤ j)
    (hright : j < beta q - q) :
    (∀ i : ℤ, 0 ≤ i → i < q → beta i < j + q) ∧
      j + q < beta q := by
  constructor
  · intro i hi0 hiq
    have hi := hleft i hi0 hiq
    linarith
  · linarith

/-- If at most one quarter of all candidates are bad and at most one half are
    requested, enough distinct good candidates remain. -/
theorem enough_good_candidates
    (A B k : ℕ)
    (hbad : 4 * B ≤ A)
    (hblocks : 2 * k ≤ A) :
    k ≤ A - B := by
  omega

/-- A shifted candidate rank stays inside the candidate universe when both
    the requested rank and the total bad-table size are below `k`. -/
theorem shifted_rank_in_range
    (A B j q k : ℕ)
    (hj : j < k)
    (hq : q ≤ B)
    (hB : B < k)
    (hA : 2 * k ≤ A) :
    j + q < A := by
  omega

/-- Integer form of `B ≤ A / b^(2b)` followed by `A < 4k`. -/
theorem bad_table_scaled_lt
    (A B b k : ℕ)
    (hcount : B * b ^ (2 * b) ≤ A)
    (htight : A < 4 * k) :
    B * b ^ (2 * b) < 4 * k :=
  lt_of_le_of_lt hcount htight

/-- Multiplying the sparse bad-table ledger by a positive rank bitlength. -/
theorem bad_rank_comparison_ledger
    (B p k R : ℕ)
    (hcount : B * p < 4 * k)
    (hR : 0 < R) :
    (B * R) * p < (4 * k) * R := by
  calc
    (B * R) * p = (B * p) * R := by ring
    _ < (4 * k) * R := Nat.mul_lt_mul_of_pos_right hcount hR

/-- Combined finite ledger used by the entropy-tight exception-table
    compiler. -/
theorem entropy_tight_exception_ledger
    (A B b k R : ℕ)
    (hcount : B * b ^ (2 * b) ≤ A)
    (htight : A < 4 * k)
    (hR : 0 < R) :
    (B * R) * b ^ (2 * b) < (4 * k) * R := by
  apply bad_rank_comparison_ledger B (b ^ (2 * b)) k R
  · exact bad_table_scaled_lt A B b k hcount htight
  · exact hR

#print axioms shifted_threshold_step
#print axioms rank_delete_window
#print axioms enough_good_candidates
#print axioms shifted_rank_in_range
#print axioms bad_table_scaled_lt
#print axioms bad_rank_comparison_ledger
#print axioms entropy_tight_exception_ledger

end PNPCanonicalRankDeleteFinite
