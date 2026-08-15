import Mathlib

/-!
# Yu cubic shell-budget firewall

Finite real arithmetic only.  This file formalizes the hostile scaling model
behind the correction to the Type-I affine mean-shell route.

At a Type-I parabolic scale, raw spacetime velocity energy has cubic physical
weight in the radius.  A geometric raw budget can therefore be summable while
the corresponding dimensionless charge obtained after division by the cubic
normalizer remains identically one.

This does **not** formalize Navier--Stokes, Yu's filtered balance, Stokes,
trace/Poincare, a singular chain, or regularity.
-/

open Filter
open Finset
open scoped BigOperators Topology

noncomputable section

namespace NSYuCubicShellBudgetFirewall

/-- The exact raw shell-mass model for a dyadic radius ladder: `r_k^3 = 8^{-k}`. -/
def rawShellMass (k : ℕ) : ℝ := (1 / 8 : ℝ) ^ k

/-- The cubic scale normalizer in the hostile model. -/
def cubicNormalizer (k : ℕ) : ℝ := (1 / 8 : ℝ) ^ k

/-- Every finite raw-mass prefix is bounded by the geometric total `8/7`. -/
theorem raw_shell_mass_prefix_le_eight_sevenths (n : ℕ) :
    (∑ k ∈ Finset.range n, rawShellMass k) ≤ (8 : ℝ) / 7 := by
  have hpow : 0 ≤ (1 / 8 : ℝ) ^ n := pow_nonneg (by norm_num) n
  have hne : (1 / 8 : ℝ) ≠ 1 := by norm_num
  have hgeom :
      (∑ k ∈ Finset.range n, (1 / 8 : ℝ) ^ k) =
        (1 - (1 / 8 : ℝ) ^ n) / (1 - (1 / 8 : ℝ)) := by
    simpa using
      (geom_sum_Ico' (x := (1 / 8 : ℝ)) hne
        (m := 0) (n := n) (Nat.zero_le n))
  rw [show (∑ k ∈ Finset.range n, rawShellMass k) =
      (∑ k ∈ Finset.range n, (1 / 8 : ℝ) ^ k) by rfl]
  rw [hgeom]
  calc
    (1 - (1 / 8 : ℝ) ^ n) / (1 - (1 / 8 : ℝ))
        ≤ 1 / (1 - (1 / 8 : ℝ)) := by
          apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 1 - 1 / 8)
            (by norm_num : (0 : ℝ) < 1 - 1 / 8)).2
          nlinarith
    _ = (8 : ℝ) / 7 := by norm_num

/-- The cubic normalizer is strictly positive at every finite scale. -/
theorem cubic_normalizer_pos (k : ℕ) : 0 < cubicNormalizer k := by
  exact pow_pos (by norm_num) k

/-- Raw mass divided by its cubic physical scale is exactly one at every rung. -/
theorem normalized_shell_charge_eq_one (k : ℕ) :
    rawShellMass k / cubicNormalizer k = 1 := by
  have hne : cubicNormalizer k ≠ 0 := ne_of_gt (cubic_normalizer_pos k)
  exact div_self hne

/-- The normalized shell charge therefore has linear finite-prefix accumulation. -/
theorem normalized_shell_charge_prefix_eq_nat (n : ℕ) :
    (∑ k ∈ Finset.range n, rawShellMass k / cubicNormalizer k) = (n : ℝ) := by
  simp [normalized_shell_charge_eq_one]

/-- The normalized charge does not converge to zero even though every raw prefix
is bounded by `8/7`. -/
theorem finite_cubic_raw_budget_allows_persistent_normalized_plateau :
    (∀ n : ℕ,
      (∑ k ∈ Finset.range n, rawShellMass k) ≤ (8 : ℝ) / 7) ∧
    (∀ k : ℕ, rawShellMass k / cubicNormalizer k = 1) ∧
    ¬ Tendsto (fun k : ℕ => rawShellMass k / cubicNormalizer k)
      atTop (𝓝 0) := by
  constructor
  · exact raw_shell_mass_prefix_le_eight_sevenths
  constructor
  · exact normalized_shell_charge_eq_one
  · have hfun :
        (fun k : ℕ => rawShellMass k / cubicNormalizer k) =
          fun _ : ℕ => (1 : ℝ) := by
      funext k
      exact normalized_shell_charge_eq_one k
    rw [hfun]
    intro hzero
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique hone hzero
    norm_num at h10

/-- More raw scales make the normalized plateau arbitrarily expensive even while
the physical raw budget stays uniformly bounded. -/
theorem normalized_plateau_can_exceed_any_finite_level (N : ℕ) :
    (N : ℝ) ≤
      ∑ k ∈ Finset.range (N + 1), rawShellMass k / cubicNormalizer k := by
  rw [normalized_shell_charge_prefix_eq_nat]
  norm_num

#print axioms raw_shell_mass_prefix_le_eight_sevenths
#print axioms cubic_normalizer_pos
#print axioms normalized_shell_charge_eq_one
#print axioms normalized_shell_charge_prefix_eq_nat
#print axioms finite_cubic_raw_budget_allows_persistent_normalized_plateau
#print axioms normalized_plateau_can_exceed_any_finite_level

end NSYuCubicShellBudgetFirewall
