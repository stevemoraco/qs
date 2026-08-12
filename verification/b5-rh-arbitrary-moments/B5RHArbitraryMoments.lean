import Mathlib

open Finset Nat
open fwdDiff

namespace B5RHArbitraryMoments

/-- The alternating binomial measure of order `n` annihilates every power moment
of degree strictly below `n`. This is the finite-difference core of the
arbitrary-fixed-moment nonfaithfulness obstruction. -/
theorem alternating_binomial_moment_zero {j n : ℕ} (hjn : j < n) :
    (∑ k ∈ Finset.range (n + 1),
      (((-1 : ℤ) ^ (n - k) * (n.choose k : ℤ)) * (k : ℤ) ^ j)) = 0 := by
  have hdiff :
      Δ_[(1 : ℤ)]^[n] (fun r : ℤ ↦ r ^ j) = 0 :=
    fwdDiff_iter_pow_eq_zero_of_lt hjn
  have hval :
      Δ_[(1 : ℤ)]^[n] (fun r : ℤ ↦ r ^ j) 0 = 0 := by
    rw [hdiff]
    rfl
  rw [fwdDiff_iter_eq_sum_shift] at hval
  simpa using hval

#print axioms alternating_binomial_moment_zero

/-- At the first unannihilated degree, the same alternating binomial moment is
exactly `n!`, so the two sign parts are genuinely different. -/
theorem alternating_binomial_moment_top (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (((-1 : ℤ) ^ (n - k) * (n.choose k : ℤ)) * (k : ℤ) ^ n)) = (n ! : ℤ) := by
  have hdiff := congrFun (fwdDiff_iter_eq_factorial (R := ℤ) (n := n)) 0
  rw [fwdDiff_iter_eq_sum_shift] at hdiff
  simpa using hdiff

#print axioms alternating_binomial_moment_top

end B5RHArbitraryMoments
