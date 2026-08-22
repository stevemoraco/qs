import Mathlib

/-!
# Finite algebra for the Fejer--Riesz depth optimizer

This file records only scalar and coefficient identities used by
`FEJER_RIESZ_L2_OPTIMAL_NO_BLIND_TRANSLATION_FILTER_2026-08-11.md`.
It does not formalize Fejer--Riesz factorization, the rank-two Hilbert-space
minimization, Descartes' rule, the zeta zero sum, or RH.
-/

namespace RHProof
namespace FejerRieszDepthOptimizer

/-- The closed optimizer coefficients are anti-palindromic. -/
theorem reflected_coefficient
    (R : ℝ) (N k : ℕ) (hk : k ≤ N) :
    R ^ (N - (N - k)) - R ^ (N - k) =
      -(R ^ (N - k) - R ^ k) := by
  have hsub : N - (N - k) = k := by omega
  rw [hsub]
  ring

/-- An anti-reciprocal polynomial value has strictly negative reflected
product away from its positive zero. -/
theorem anti_reciprocal_product_negative
    (r p q : ℝ) (N : ℕ)
    (hr : 0 < r) (hp : p ≠ 0)
    (hrec : q = -(r ^ N)⁻¹ * p) :
    q * p < 0 := by
  rw [hrec]
  have hrpow : 0 < r ^ N := pow_pos hr N
  have hinv : 0 < (r ^ N)⁻¹ := inv_pos.mpr hrpow
  have hp2 : 0 < p ^ 2 := sq_pos_of_ne_zero hp
  nlinarith

/-- Algebraic form of the two nonzero eigenvalues of the symmetric rank-two
operator. -/
theorem rank_two_eigenvalue_product
    (A B C s : ℝ) (hs : s ^ 2 = A * B) :
    ((C - s) / 2) * ((C + s) / 2) = (C ^ 2 - A * B) / 4 := by
  nlinarith

/-- The smaller rank-two eigenvalue is nonpositive whenever the geometric
mean dominates the correlation. -/
theorem lower_eigenvalue_nonpositive
    (C s : ℝ) (h : C ≤ s) :
    (C - s) / 2 ≤ 0 := by
  linarith

/-- Strict domination gives a strictly negative depth signal. -/
theorem lower_eigenvalue_negative
    (C s : ℝ) (h : C < s) :
    (C - s) / 2 < 0 := by
  linarith

/-- Fixed-support refinement converts a cubic discrete variance into a linear
channel-count factor after the grid spacing is `H/N`. -/
theorem fixed_support_shallow_scaling
    (N H y : ℝ) (hN : N ≠ 0) :
    (N ^ 3 / 12) * (2 * H * y / N) ^ 2 = N * H ^ 2 * y ^ 2 / 3 := by
  field_simp
  ring

end FejerRieszDepthOptimizer
end RHProof
