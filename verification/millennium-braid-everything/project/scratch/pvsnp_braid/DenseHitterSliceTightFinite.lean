import Mathlib

namespace PvsNPBraid

/-- Exact gate accounting for shared block minterms, one conjunction per
accepted projected pattern, and a final OR. -/
theorem shared_block_lookup_count
    (q precompute s : ℤ) :
    q * precompute + s * (q - 1) + (s - 1) =
      q * (precompute + s) - 1 := by
  ring

/-- Substituting the safe per-block precomputation budget gives the displayed
lookup bound. -/
theorem shared_block_lookup_safe
    (q powBlock b s : ℤ) :
    q * (powBlock + b) + s * (q - 1) + (s - 1) =
      q * (powBlock + b + s) - 1 := by
  ring

/-- If the power-table cost is at most twice the pattern count, the total
per-block budget is at most `3s+b`. -/
theorem optimized_block_budget
    (powBlock b s : ℤ)
    (hpow : powBlock ≤ 2 * s) :
    powBlock + b + s ≤ 3 * s + b := by
  linarith

/-- The union-bound threshold is exactly the logarithmic circuit-count budget
divided by the log inverse density. -/
theorem union_bound_exponent
    (logN m logInvRho : ℝ)
    (h : logN < m * logInvRho) :
    logN - m * logInvRho < 0 := by
  linarith

/-- The CLY scale arithmetic: dividing a linear gate budget times `log n` by
`log^2 n / loglog n` leaves `n loglog n / log n`. -/
theorem cly_scale_cancellation
    (n logn loglogn c : ℝ)
    (hlogn : logn ≠ 0) :
    (c * n * logn) / (logn ^ 2 / loglogn) =
      c * n * loglogn / logn := by
  field_simp [hlogn]
  ring

end PvsNPBraid
