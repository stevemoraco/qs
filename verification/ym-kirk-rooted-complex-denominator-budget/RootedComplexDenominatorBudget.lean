import Mathlib

namespace Millennium.YangMills

/-!
# Rooted complex-denominator budget

Finite scalar firewall for the compact Haar-pivot repair.

A rooted/local polymer gas can have a normalization inverse whose total cost is
extensive in the number `n` of selected pivots.  This is not by itself fatal:
if each clean pivot contributes a contraction `theta`, an inverse cost bounded
by `q^n` is absorbed exactly into the new per-pivot base `theta*q`.

This is the correct finite algebra behind a complex zero-free/KP repair of the
compact denominator.  It does not prove a KP theorem, Kirk's complex compact
activity row, Theorem 6.43, Osterwalder--Schrader reconstruction, the Yang--Mills
mass gap, or a Clay theorem.
-/

/-- An extensive inverse-normalization cost is absorbed into the per-pivot
contraction base. -/
theorem rooted_inverse_cost_absorbed
    (theta q invD : ℝ)
    (n : ℕ)
    (htheta : 0 ≤ theta)
    (hinv : invD ≤ q ^ n) :
    theta ^ n * invD ≤ (theta * q) ^ n := by
  have hpow : 0 ≤ theta ^ n := pow_nonneg htheta n
  calc
    theta ^ n * invD ≤ theta ^ n * q ^ n :=
      mul_le_mul_of_nonneg_left hinv hpow
    _ = (theta * q) ^ n := by
      rw [mul_pow]

/-- Exponential per-pivot inverse cost is just another fixed factor in the
per-pivot contraction base. -/
theorem exponential_rooted_inverse_cost_absorbed
    (theta c invD : ℝ)
    (n : ℕ)
    (htheta : 0 ≤ theta)
    (hinv : invD ≤ (Real.exp c) ^ n) :
    theta ^ n * invD ≤ (theta * Real.exp c) ^ n := by
  exact rooted_inverse_cost_absorbed theta (Real.exp c) invD n htheta hinv

/-- Concrete witness: a factor two of inverse-normalization cost per pivot is
still compatible with geometric decay when the clean-pivot contraction is
`1/4`; the combined base is exactly `1/2`. -/
theorem quarter_contraction_pays_twofold_inverse
    (n : ℕ) :
    ((1 : ℝ) / 4) ^ n * 2 ^ n = ((1 : ℝ) / 2) ^ n := by
  rw [← mul_pow]
  norm_num

#print axioms rooted_inverse_cost_absorbed
#print axioms exponential_rooted_inverse_cost_absorbed
#print axioms quarter_contraction_pays_twofold_inverse

end Millennium.YangMills
