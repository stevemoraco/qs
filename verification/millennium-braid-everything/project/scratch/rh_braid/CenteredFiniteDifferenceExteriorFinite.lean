import Mathlib

/-!
# Finite algebra for the centered finite-difference exterior RH detector

This file records only scalar sign/comparison lemmas.  The analytic zero sum,
positive-definiteness argument, exact exponential type, explicit formula, and RH
implications are banked separately and are not formalized here.
-/

namespace RHProof
namespace CenteredFiniteDifferenceExterior

/-- A centered-difference spectral weight written as a square is nonnegative. -/
theorem real_pair_multiplier_nonnegative
    (s h : ℝ) (hh : h ≠ 0) :
    0 ≤ 4 * s^2 / h^2 := by
  positivity

/-- Once the hyperbolic sine factor is known nonzero, the reflected-pair
centered-difference coefficient is strictly negative. -/
theorem reflected_pair_multiplier_negative
    (m n s h : ℝ)
    (hm : 0 < m) (hn : 0 < n) (hs : s ≠ 0) (hh : 0 < h) :
    -4 * m^2 * n^4 * s^2 / h^2 < 0 := by
  have hs2 : 0 < s^2 := sq_pos_of_ne_zero hs
  have hh2 : 0 < h^2 := sq_pos_of_pos hh
  positivity

/-- Abstract comparison core for the fact that the normalized hyperbolic
finite-difference factor strictly dominates the quadratic curvature factor.
In the analytic application `s = sinh (y*h)` and the premise follows from
`|sinh u| > |u|` for `u ≠ 0`. -/
theorem normalized_reflection_amplification
    (y h s : ℝ) (hh : 0 < h)
    (hs : (y * h)^2 < s^2) :
    4 * y^2 < 4 * s^2 / h^2 := by
  have hh2 : 0 < h^2 := sq_pos_of_pos hh
  apply (lt_div_iff₀ hh2).2
  nlinarith [hs]

/-- Abstract comparison core for attenuation of an on-line real spectral
weight.  In the analytic application `s = sin (d*h/2)` and the premise is
`|sin u| ≤ |u|`. -/
theorem normalized_real_pair_attenuation
    (d h s : ℝ) (hh : 0 < h)
    (hs : s^2 ≤ (d * h / 2)^2) :
    4 * s^2 / h^2 ≤ d^2 := by
  have hh2 : 0 < h^2 := sq_pos_of_pos hh
  apply (div_le_iff₀ hh2).2
  nlinarith [hs]

/-- A convex positive mixture of quantities individually bounded by `Q` is
still bounded by `Q`.  This is the finite bookkeeping core behind the theorem
that interior centered steps cannot beat the outermost admissible step. -/
theorem convex_mixture_le
    {ι : Type*} (s : Finset ι) (a q : ι → ℝ) (Q : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hq : ∀ i ∈ s, q i ≤ Q)
    (hsum : ∑ i in s, a i = 1) :
    ∑ i in s, a i * q i ≤ Q := by
  calc
    ∑ i in s, a i * q i ≤ ∑ i in s, a i * Q := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hq i hi) (ha i hi)
    _ = Q := by
      rw [← Finset.sum_mul, hsum, one_mul]

/-- The first centered power has the desired negative reflected sign. -/
theorem reflected_power_one_negative
    (q : ℝ) (hq : 0 < q) : -q < 0 := by
  linarith

/-- The second centered power flips to the wrong positive sign. -/
theorem reflected_power_two_positive
    (q : ℝ) (hq : 0 < q) : 0 < q^2 := by
  positivity

/-- The third centered power returns to the negative sign but at sixth order
in the shallow-depth parameter. -/
theorem reflected_power_three_negative
    (q : ℝ) (hq : 0 < q) : -(q^3) < 0 := by
  positivity

end CenteredFiniteDifferenceExterior
end RHProof
