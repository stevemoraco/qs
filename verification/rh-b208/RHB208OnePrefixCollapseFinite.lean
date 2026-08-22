import Mathlib

/-!
# RH B208 one-prefix / Zhao-state finite core

Finite algebra behind collapsing B207's two prefix scalars to one positive-coefficient
prefix and then to one mean-Mertens state, up to explicit deterministic corrections.

No primes, Zhao theorem, asymptotics, BGST, B46, zeta, RH, or negation of RH are
formalized here.
-/

namespace RHB208OnePrefixCollapseFinite

/-- Exact two-prefix to one-prefix decomposition. -/
theorem two_prefix_to_one_prefix
    {A U Theta x h : ℝ} (hx : x ≠ 0) :
    A * U - h * Theta =
      A * (U - Theta / x) + (A / x - h) * Theta := by
  field_simp [hx]
  ring

/-- If the block average square dominates the left endpoint square and the
prime-counting prefix is nonnegative, the endpoint correction is nonnegative. -/
theorem endpoint_correction_nonnegative
    {A x h Theta : ℝ}
    (hx : 0 < x)
    (hA : h * x ≤ A)
    (hTheta : 0 ≤ Theta) :
    0 ≤ (A / x - h) * Theta := by
  have hdiv : h ≤ A / x := by
    exact (le_div_iff₀ hx).2 hA
  exact mul_nonneg (sub_nonneg.mpr hdiv) hTheta

/-- Exact algebraic passage from one prefix `V` to one mean state `A1`.
`L` stands for the finite weighted logarithmic block term. -/
theorem one_prefix_to_mean_state
    {x A h V logx c C A1 L : ℝ}
    (hx : x ≠ 0)
    (hA1 : A1 = x * V - x * logx + (1 - c) * x + C) :
    A * V + (-2 * L + (1 - c) * A + h * C) =
      (A / x) * A1 + A * logx - 2 * L + C * (h - A / x) := by
  rw [hA1]
  field_simp [hx]
  ring

/-- Deleting a nonnegative correction preserves any negative shifted block. -/
theorem negative_shift_survives_positive_deletion
    {core correction T : ℝ}
    (hcorrection : 0 ≤ correction)
    (hneg : core + correction + T < 0) :
    core + T < 0 := by
  linarith

/-- If the true block is nonnegative and the total deleted positive correction is
smaller than the threshold, the reduced shifted block stays positive. -/
theorem small_positive_deletion_protects_shift
    {core correction T : ℝ}
    (hT : 0 < T)
    (htrue : 0 ≤ core + correction)
    (hsmall : correction < T) :
    0 < core + T := by
  linarith

/-- A deterministic perturbation smaller than half the threshold cannot turn a
mean-state value below `-T` into a nonnegative reduced block. -/
theorem mean_state_margin_transfer
    {mean correction T : ℝ}
    (hT : 0 < T)
    (hsmall : |correction| < T / 2)
    (hmean : mean + 3 * T / 2 < 0) :
    mean + correction + T < 0 := by
  have hupper : correction < T / 2 := lt_of_le_of_lt (le_abs_self correction) hsmall
  linarith

#print axioms two_prefix_to_one_prefix
#print axioms endpoint_correction_nonnegative
#print axioms one_prefix_to_mean_state
#print axioms negative_shift_survives_positive_deletion
#print axioms small_positive_deletion_protects_shift
#print axioms mean_state_margin_transfer

end RHB208OnePrefixCollapseFinite
