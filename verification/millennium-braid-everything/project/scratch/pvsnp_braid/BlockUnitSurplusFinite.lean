import Mathlib

namespace PvsNPBraid

/-- The `-2` inner deficits cancel the outer `2b` baseline, so block
composition transfers the outer absolute surplus unchanged. -/
theorem block_unit_surplus_conservation
    (b m delta : ℤ) :
    b * (2 * m - 2) + (2 * b + delta) = 2 * (b * m) + delta := by
  ring

/-- A constant-factor outer lower bound `c b` has surplus `(c-2)b` above the
`2b` baseline. -/
theorem outer_linear_surplus
    (b c : ℤ) :
    c * b - 2 * b = (c - 2) * b := by
  ring

/-- One outer positive pattern of weight `k` creates `m^k` inner
realizations. -/
theorem one_pattern_lift_count (m k : ℕ) :
    (∏ _i ∈ Finset.range k, m) = m ^ k := by
  simp

/-- Reapplying an unchanged-surplus composition step cannot amplify the
surplus. -/
theorem recursive_surplus_fixed
    (delta : ℤ) (levels : ℕ) :
    (Function.iterate (fun x : ℤ => x) levels) delta = delta := by
  simp

end PvsNPBraid
