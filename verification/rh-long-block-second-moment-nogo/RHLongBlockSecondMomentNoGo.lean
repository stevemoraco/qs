import Mathlib

/-!
# RH long-block second-moment no-go

This file formalizes the finite arithmetic core of the countermodel banked in
`stevemoraco/RH`. It proves that perfectly centered positive gap data can have
linear one-point square energy but quadratic coherent moving-block mass.

It does not formalize primes, prime gaps, Stadlmann's theorem, the prime-entry
criterion, or the Riemann hypothesis.
-/

open scoped BigOperators

namespace RHLongBlockSecondMomentNoGo

/-- Two equally long constant gap blocks have exactly the prescribed mean. -/
theorem gap_sum_identity (M L : ℤ) :
    2 * M * (L - 1) + 2 * M * (L + 1) = 4 * M * L := by
  ring

/-- Their individual gap-square budget is linear in the block length. -/
theorem gap_square_identity (M L : ℤ) :
    2 * M * ((L - 1) ^ 2 + (L + 1) ^ 2) =
      4 * M * (L ^ 2 + 1) := by
  ring

/-- The associated `+1` block followed by a `-1` block is exactly centered. -/
theorem centered_increment_identity (M : ℤ) :
    2 * M * 1 + 2 * M * (-1) = 0 := by
  ring

/-- A length-`2M` window containing `2M-t` positive increments and `t`
negative increments has value `2M-2t`. -/
theorem moving_window_value (M t : ℤ) :
    (2 * M - t) * 1 + t * (-1) = 2 * M - 2 * t := by
  ring

/-- Those window values are nonnegative for the coherent endpoint range
`0 ≤ t ≤ M`. -/
theorem moving_window_nonnegative {M t : ℕ} (ht : t ≤ M) :
    (0 : ℤ) ≤ 2 * (M : ℤ) - 2 * (t : ℤ) := by
  omega

/-- Exact quadratic positive-block mass:
`sum_{t=0}^{M} (2M-2t) = M(M+1)`. -/
theorem block_mass_identity (M : ℕ) :
    (∑ t ∈ Finset.range (M + 1), 2 * (M - t)) = M * (M + 1) := by
  calc
    (∑ t ∈ Finset.range (M + 1), 2 * (M - t)) =
        ∑ t ∈ Finset.range (M + 1), 2 * t := by
          simpa using
            (Finset.sum_range_reflect (fun t : ℕ => 2 * t) (M + 1))
    _ = 2 * (∑ t ∈ Finset.range (M + 1), t) := by
          rw [Finset.mul_sum]
    _ = M * (M + 1) := by
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            (Finset.sum_range_id_mul_two (M + 1))

/-- For every proposed constant `C` and fixed gap baseline `L`, an explicit
block length defeats a linear bound by the individual square budget. -/
theorem no_uniform_linear_moment_bound_witness (C L : ℕ) :
    let M := 4 * C * (L ^ 2 + 1) + 1
    C * (4 * M * (L ^ 2 + 1)) < M * (M + 1) := by
  dsimp
  nlinarith

#print axioms gap_sum_identity
#print axioms gap_square_identity
#print axioms centered_increment_identity
#print axioms moving_window_value
#print axioms moving_window_nonnegative
#print axioms block_mass_identity
#print axioms no_uniform_linear_moment_bound_witness

end RHLongBlockSecondMomentNoGo
