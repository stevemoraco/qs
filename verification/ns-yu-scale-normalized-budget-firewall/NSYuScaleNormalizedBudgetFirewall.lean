import Mathlib

/-!
# Yu scale-normalized budget firewall

This file formalizes finite real arithmetic behind the next hostile audit of the
filtered-vorticity lane.

A sparse geometric sequence of Type-I peak times can have disjoint fixed-fraction
parabolic cores.  Nevertheless, a persistent scale-normalized charge can cost
only a summable amount in the underlying physical budget: if the physical mass
at radius `r_k` is `r_k`, then the normalized charge `mass_k / r_k` is identically
one while the total physical mass is bounded by a geometric series.

This proves that bounded overlap plus the ordinary radius-weighted Leray budget
does not force Yu's normalized reservoir or diffusion charge to vanish.  A proof
needs an unweighted/Carleson estimate in the normalized currency or another
rigidity mechanism.

These declarations do **not** formalize Navier--Stokes, Leray dissipation, Yu's
PDE inequalities, a singular chain, or regularity.
-/

open Filter
open Finset
open scoped BigOperators Topology

namespace NSYuScaleNormalizedBudgetFirewall

/-- Left endpoint of the fixed-fraction parabolic core centered at time `-r²`. -/
def coreLeft (c r : ℝ) : ℝ := -(1 + c) * r ^ 2

/-- Right endpoint of the fixed-fraction parabolic core centered at time `-r²`. -/
def coreRight (c r : ℝ) : ℝ := -(1 - c) * r ^ 2

/-- A positive fractional core has nonempty time interior. -/
theorem core_interval_nonempty
    {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    coreLeft c r < coreRight c r := by
  have hr2 : 0 < r ^ 2 := by positivity
  dsimp [coreLeft, coreRight]
  nlinarith

/-- Exact one-step separation criterion.  If
`(1+c) q² < 1-c`, then the core at radius `q r` begins strictly after the core
at radius `r` ends. -/
theorem core_intervals_one_step_disjoint
    {c q r : ℝ} (hr : 0 < r)
    (hsep : (1 + c) * q ^ 2 < 1 - c) :
    coreRight c r < coreLeft c (q * r) := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hmul := mul_lt_mul_of_pos_right hsep hr2
  dsimp [coreLeft, coreRight]
  nlinarith

/-- Finite geometric physical masses have a uniform prefix bound. -/
theorem geometric_physical_mass_prefix_bound
    (r0 q : ℝ) (hr0 : 0 ≤ r0) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, r0 * q ^ k) ≤ r0 / (1 - q) := by
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hpow : 0 ≤ q ^ n := pow_nonneg hq0 n
  have hgeom :
      (∑ k ∈ Finset.range n, q ^ k) ≤ 1 / (1 - q) := by
    rw [geom_sum_of_lt_one hq1]
    apply (div_le_div_iff₀ hden).2
    nlinarith
  calc
    (∑ k ∈ Finset.range n, r0 * q ^ k) =
        r0 * (∑ k ∈ Finset.range n, q ^ k) := by
          rw [Finset.mul_sum]
    _ ≤ r0 * (1 / (1 - q)) :=
      mul_le_mul_of_nonneg_left hgeom hr0
    _ = r0 / (1 - q) := by ring

/-- Every radius on a positive geometric ladder is positive. -/
theorem geometric_radius_positive
    {r0 q : ℝ} (hr0 : 0 < r0) (hq0 : 0 < q) (k : ℕ) :
    0 < r0 * q ^ k := by
  exact mul_pos hr0 (pow_pos hq0 k)

/-- Taking physical mass equal to radius gives normalized charge exactly one at
every scale. -/
theorem geometric_mass_has_unit_normalized_charge
    {r0 q : ℝ} (hr0 : 0 < r0) (hq0 : 0 < q) (k : ℕ) :
    (r0 * q ^ k) / (r0 * q ^ k) = 1 := by
  have hne : r0 * q ^ k ≠ 0 :=
    ne_of_gt (geometric_radius_positive hr0 hq0 k)
  exact div_self hne

/-- A constant unit charge does not converge to zero. -/
theorem unit_charge_not_tendsto_zero :
    ¬ Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
  intro hzero
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique hone hzero
  norm_num at h10

/-- The exact hostile countermodel: all physical-mass prefixes are uniformly
bounded, every normalized charge is one, and the normalized charges do not tend
to zero. -/
theorem finite_physical_budget_allows_persistent_normalized_charge
    (r0 q : ℝ) (hr0 : 0 < r0) (hq0 : 0 < q) (hq1 : q < 1) :
    (∀ n : ℕ,
      (∑ k ∈ Finset.range n, r0 * q ^ k) ≤ r0 / (1 - q)) ∧
    (∀ k : ℕ, (r0 * q ^ k) / (r0 * q ^ k) = 1) ∧
    ¬ Tendsto (fun k : ℕ => (r0 * q ^ k) / (r0 * q ^ k))
      atTop (𝓝 0) := by
  constructor
  · intro n
    exact geometric_physical_mass_prefix_bound r0 q hr0.le hq0.le hq1 n
  constructor
  · intro k
    exact geometric_mass_has_unit_normalized_charge hr0 hq0 k
  · have hfun :
        (fun k : ℕ => (r0 * q ^ k) / (r0 * q ^ k)) =
          fun _ : ℕ => (1 : ℝ) := by
      funext k
      exact geometric_mass_has_unit_normalized_charge hr0 hq0 k
    rw [hfun]
    exact unit_charge_not_tendsto_zero

/-- The same obstruction at any nonnegative persistent charge `delta`. -/
theorem persistent_delta_charge_has_finite_physical_prefix
    (delta r0 q : ℝ)
    (hdelta : 0 ≤ delta) (hr0 : 0 < r0) (hq0 : 0 < q) (hq1 : q < 1) :
    (∀ n : ℕ,
      (∑ k ∈ Finset.range n, delta * (r0 * q ^ k)) ≤
        delta * (r0 / (1 - q))) ∧
    (∀ k : ℕ,
      (delta * (r0 * q ^ k)) / (r0 * q ^ k) = delta) := by
  constructor
  · intro n
    calc
      (∑ k ∈ Finset.range n, delta * (r0 * q ^ k)) =
          delta * (∑ k ∈ Finset.range n, r0 * q ^ k) := by
            rw [Finset.mul_sum]
      _ ≤ delta * (r0 / (1 - q)) := by
        exact mul_le_mul_of_nonneg_left
          (geometric_physical_mass_prefix_bound r0 q hr0.le hq0.le hq1 n)
          hdelta
  · intro k
    have hne : r0 * q ^ k ≠ 0 :=
      ne_of_gt (geometric_radius_positive hr0 hq0 k)
    field_simp [hne]

#print axioms core_interval_nonempty
#print axioms core_intervals_one_step_disjoint
#print axioms geometric_physical_mass_prefix_bound
#print axioms geometric_radius_positive
#print axioms geometric_mass_has_unit_normalized_charge
#print axioms unit_charge_not_tendsto_zero
#print axioms finite_physical_budget_allows_persistent_normalized_charge
#print axioms persistent_delta_charge_has_finite_physical_prefix

end NSYuScaleNormalizedBudgetFirewall
