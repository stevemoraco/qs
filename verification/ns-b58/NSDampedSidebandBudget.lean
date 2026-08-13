import Mathlib

namespace NSDampedSidebandBudget

open scoped BigOperators

/-- Scalar Young inequality with the damping weight written in the exact form
used by the sideband energy estimate. -/
theorem weighted_young
    {g z gamma : ℝ} (hgamma : 0 < gamma) :
    2 * g * z ≤ g ^ 2 / gamma + gamma * z ^ 2 := by
  have hsq : 0 ≤ (g - gamma * z) ^ 2 := sq_nonneg (g - gamma * z)
  have hrewrite :
      g ^ 2 / gamma + gamma * z ^ 2 =
        (g ^ 2 + gamma ^ 2 * z ^ 2) / gamma := by
    field_simp [ne_of_gt hgamma]
    <;> ring
  rw [hrewrite]
  apply (le_div_iff₀ hgamma).2
  nlinarith

/-- Finite-network Young inequality with channel-dependent positive weights. -/
theorem finite_weighted_young
    {κ : Type*} [DecidableEq κ]
    (J : Finset κ) (g z gamma : κ → ℝ)
    (hgamma : ∀ j ∈ J, 0 < gamma j) :
    2 * (∑ j ∈ J, g j * z j) ≤
      (∑ j ∈ J, (g j) ^ 2 / gamma j) +
        ∑ j ∈ J, gamma j * (z j) ^ 2 := by
  calc
    2 * (∑ j ∈ J, g j * z j) =
        ∑ j ∈ J, 2 * g j * z j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ ≤ ∑ j ∈ J, ((g j) ^ 2 / gamma j + gamma j * (z j) ^ 2) := by
          exact Finset.sum_le_sum fun j hj => weighted_young (hgamma j hj)
    _ = (∑ j ∈ J, (g j) ^ 2 / gamma j) +
          ∑ j ∈ J, gamma j * (z j) ^ 2 := by
          rw [Finset.sum_add_distrib]

/-- If the actual damping is at least `gamma`, the energy derivative receives
one full coercive `-gamma*z^2` term after Young's inequality. -/
theorem damped_scalar_budget
    {g z gamma Gamma : ℝ}
    (hgamma : 0 < gamma)
    (hfloor : gamma ≤ Gamma) :
    2 * g * z - 2 * Gamma * z ^ 2 ≤
      g ^ 2 / gamma - gamma * z ^ 2 := by
  have hyoung := weighted_young (g := g) (z := z) hgamma
  have hextra : 0 ≤ 2 * (Gamma - gamma) * z ^ 2 := by positivity
  nlinarith

/-- Finite sum of the pointwise damped budgets. -/
theorem finite_damped_budget
    {κ : Type*} [DecidableEq κ]
    (J : Finset κ) (g z Gamma : κ → ℝ)
    {gamma : ℝ}
    (hgamma : 0 < gamma)
    (hfloor : ∀ j ∈ J, gamma ≤ Gamma j) :
    (∑ j ∈ J, (2 * g j * z j - 2 * Gamma j * (z j) ^ 2)) ≤
      (∑ j ∈ J, (g j) ^ 2 / gamma) -
        gamma * (∑ j ∈ J, (z j) ^ 2) := by
  calc
    (∑ j ∈ J, (2 * g j * z j - 2 * Gamma j * (z j) ^ 2)) ≤
        ∑ j ∈ J, ((g j) ^ 2 / gamma - gamma * (z j) ^ 2) := by
          exact Finset.sum_le_sum fun j hj =>
            damped_scalar_budget hgamma (hfloor j hj)
    _ = (∑ j ∈ J, (g j) ^ 2 / gamma) -
          gamma * (∑ j ∈ J, (z j) ^ 2) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]

#print axioms weighted_young
#print axioms finite_weighted_young
#print axioms damped_scalar_budget
#print axioms finite_damped_budget

end NSDampedSidebandBudget
