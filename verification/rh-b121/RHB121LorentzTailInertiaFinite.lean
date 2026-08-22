import Mathlib

/-!
# RH B121 Lorentz-tail / shifted-inertia finite core

This file formalizes only finite real-algebra pieces used by the B121 reduction:

* a threshold exceedance set pays its threshold times its cardinality;
* a factor-two depth bracket transfers a tail score with only factor-two loss;
* a metric shift transports exactly under scalar congruence;
* transported positive/negative signs are preserved;
* shifting by the ambient identity instead of the transported metric can reverse
  the sign after congruence.

It does **not** formalize primes, von Mangoldt weights, the B46 kernel, Lorentz
spaces, matrix inertia, contour Hankel matrices, zeta, or the Riemann hypothesis.
-/

open Finset
open scoped BigOperators

namespace RHB121LorentzTailInertiaFinite

/-- Every member of a finite exceedance set contributes at least the threshold. -/
theorem threshold_subset_payment
    {ι : Type*} (s : Finset ι) (x : ι → ℝ) (lambda : ℝ)
    (hx : ∀ i ∈ s, lambda ≤ x i) :
    lambda * (s.card : ℝ) ≤ ∑ i ∈ s, x i := by
  have hsum : (∑ i ∈ s, lambda) ≤ ∑ i ∈ s, x i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hx i hi
  simpa [mul_comm] using hsum

/-- If `lambda` lies in the factor-two interval `[a,2a]` and `u ≤ v`, then the
corresponding threshold score loses at most the same factor two. -/
theorem dyadic_bracket_score
    {a lambda u v : ℝ}
    (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hlambda : lambda ≤ 2 * a) (huv : u ≤ v) :
    lambda * u ≤ 2 * a * v := by
  have h1 : lambda * u ≤ (2 * a) * u :=
    mul_le_mul_of_nonneg_right hlambda hu
  have h2 : (2 * a) * u ≤ (2 * a) * v := by
    exact mul_le_mul_of_nonneg_left huv (mul_nonneg (by norm_num) ha)
  exact h1.trans h2

/-- The scalar identity behind a congruence-safe generalized shift:
`Sᵀ(A+lambda G)S = SᵀAS + lambda SᵀGS`. -/
theorem transported_metric_shift_factor
    (a g lambda s : ℝ) :
    s ^ 2 * a + lambda * s ^ 2 * g = s ^ 2 * (a + lambda * g) := by
  ring

/-- A nonnegative source pencil remains nonnegative after scalar congruence. -/
theorem transported_metric_shift_preserves_nonnegative
    {a g lambda s : ℝ}
    (hsource : 0 ≤ a + lambda * g) :
    0 ≤ s ^ 2 * a + lambda * s ^ 2 * g := by
  rw [transported_metric_shift_factor]
  exact mul_nonneg (sq_nonneg s) hsource

/-- A strictly negative source pencil remains strictly negative under a
nondegenerate scalar congruence. -/
theorem transported_metric_shift_preserves_negative
    {a g lambda s : ℝ}
    (hs : s ≠ 0) (hsource : a + lambda * g < 0) :
    s ^ 2 * a + lambda * s ^ 2 * g < 0 := by
  rw [transported_metric_shift_factor]
  have hs2 : 0 < s ^ 2 := sq_pos_of_ne_zero hs
  exact mul_neg_of_pos_of_neg hs2 hsource

/-- Exact one-dimensional hostile witness: an ambient identity shift can change
sign after congruence, whereas the transported metric shift preserves it. -/
theorem ambient_identity_shift_is_not_congruence_invariant :
    ((-1 : ℝ) + 2 = 1) ∧
    ((2 : ℝ) ^ 2 * (-1) + 2 = -2) ∧
    ((2 : ℝ) ^ 2 * (-1) + 2 * (2 : ℝ) ^ 2 = 4) := by
  norm_num

/-- A positive depth can lie entirely below one fixed positive threshold.  This
is the scalar firewall behind the need for a moving/diverging threshold family
when only shifted sign counts are available. -/
theorem fixed_positive_threshold_can_miss_depth
    {x lambda : ℝ} (hx : 0 < x) (hbelow : x < lambda) :
    0 < x ∧ ¬ (lambda < x) := by
  exact ⟨hx, not_lt.mpr (le_of_lt hbelow)⟩

#print axioms threshold_subset_payment
#print axioms dyadic_bracket_score
#print axioms transported_metric_shift_factor
#print axioms transported_metric_shift_preserves_nonnegative
#print axioms transported_metric_shift_preserves_negative
#print axioms ambient_identity_shift_is_not_congruence_invariant
#print axioms fixed_positive_threshold_can_miss_depth

end RHB121LorentzTailInertiaFinite
