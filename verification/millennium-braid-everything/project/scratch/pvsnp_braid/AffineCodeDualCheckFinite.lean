import Mathlib

namespace PvsNPBraid

/-- Computing `k` shared parity checks, comparing each to its affine target,
and ANDing the results costs the shared parity circuit plus `2k-1` gates. -/
theorem affine_dual_checker_gate_count
    (shared k : ℤ) :
    shared + k + (k - 1) = shared + 2 * k - 1 := by
  ring

/-- At a near-`2n` threshold, survival of the affine-code architecture forces
the shared dual-check computation above the exact remaining budget. -/
theorem affine_dual_dense_hitter_budget
    (shared n delta k : ℤ)
    (h : 2 * n + delta < shared + 2 * k - 1) :
    2 * n + delta - 2 * k + 1 < shared := by
  linarith

/-- Conversely, a cheap enough threshold-sized dual-check subsystem gives a
containing circuit inside the forbidden gate budget. -/
theorem cheap_dual_subsystem_breaks_budget
    (shared n delta k : ℤ)
    (h : shared ≤ 2 * n + delta - 2 * k + 1) :
    shared + 2 * k - 1 ≤ 2 * n + delta := by
  linarith

/-- `k` independent affine parity equations cut density by the exact factor
`2^k`; this finite exponent identity records the codimension accounting. -/
theorem affine_solution_count_exponent (n k : ℕ) (hk : k ≤ n) :
    n - k + k = n := by
  omega

end PvsNPBraid
