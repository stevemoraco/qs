import Mathlib

namespace Millennium.YangMills.TreeReserveReplay

/-- For `n ≥ 2`, the number of incidences is at most twice the number of
non-root incidences. -/
theorem incidence_le_twice_nonroot (n : ℕ) (hn : 2 ≤ n) :
    n ≤ 2 * (n - 1) := by
  omega

/-- A fixed incidence charge is absorbed by a linear support reserve. -/
theorem pivot_incidence_charge_absorbed
    (lambda mu cp R : ℝ) (n : ℕ)
    (hn : 2 ≤ n)
    (hlambda : 0 ≤ lambda)
    (hscale : 2 * lambda ≤ mu * cp * R) :
    lambda * (n : ℝ) ≤ mu * cp * R * ((n - 1 : ℕ) : ℝ) := by
  have hnNat : n ≤ 2 * (n - 1) := incidence_le_twice_nonroot n hn
  have hnReal : (n : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnNat
  have hnonroot : 0 ≤ ((n - 1 : ℕ) : ℝ) := by positivity
  calc
    lambda * (n : ℝ) ≤ lambda * (2 * ((n - 1 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hnReal hlambda
    _ = (2 * lambda) * ((n - 1 : ℕ) : ℝ) := by ring
    _ ≤ (mu * cp * R) * ((n - 1 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_right hscale hnonroot

/-- A tree/support reserve can pay a pivot-incidence charge while retaining a
weaker diameter exponent. -/
theorem tree_reserve_pays_incidence_and_leaves_diameter
    (lambda aTree mDiam cp R treeCost diamCost : ℝ) (n : ℕ)
    (hn : 2 ≤ n)
    (hlambda : 0 ≤ lambda)
    (hgap : 0 ≤ aTree - mDiam)
    (hmDiam : 0 ≤ mDiam)
    (hscale : 2 * lambda ≤ (aTree - mDiam) * cp * R)
    (hgeom : cp * R * ((n - 1 : ℕ) : ℝ) ≤ treeCost)
    (hdiam : diamCost ≤ treeCost) :
    lambda * (n : ℝ) + mDiam * diamCost ≤ aTree * treeCost := by
  have hcharge :
      lambda * (n : ℝ) ≤
        (aTree - mDiam) * cp * R * ((n - 1 : ℕ) : ℝ) := by
    exact pivot_incidence_charge_absorbed
      lambda (aTree - mDiam) cp R n hn hlambda hscale
  have htree :
      (aTree - mDiam) * (cp * R * ((n - 1 : ℕ) : ℝ)) ≤
        (aTree - mDiam) * treeCost := by
    exact mul_le_mul_of_nonneg_left hgeom hgap
  have hchargeTree :
      lambda * (n : ℝ) ≤ (aTree - mDiam) * treeCost := by
    calc
      lambda * (n : ℝ) ≤
          (aTree - mDiam) * cp * R * ((n - 1 : ℕ) : ℝ) := hcharge
      _ = (aTree - mDiam) *
          (cp * R * ((n - 1 : ℕ) : ℝ)) := by ring
      _ ≤ (aTree - mDiam) * treeCost := htree
  have hdiamPaid : mDiam * diamCost ≤ mDiam * treeCost := by
    exact mul_le_mul_of_nonneg_left hdiam hmDiam
  calc
    lambda * (n : ℝ) + mDiam * diamCost
        ≤ (aTree - mDiam) * treeCost + mDiam * treeCost :=
          add_le_add hchargeTree hdiamPaid
    _ = aTree * treeCost := by ring

/-- Exponential form of the same bookkeeping. -/
theorem exp_incidence_times_diameter_le_tree_reserve
    (lambda aTree mDiam cp R treeCost diamCost : ℝ) (n : ℕ)
    (hn : 2 ≤ n)
    (hlambda : 0 ≤ lambda)
    (hgap : 0 ≤ aTree - mDiam)
    (hmDiam : 0 ≤ mDiam)
    (hscale : 2 * lambda ≤ (aTree - mDiam) * cp * R)
    (hgeom : cp * R * ((n - 1 : ℕ) : ℝ) ≤ treeCost)
    (hdiam : diamCost ≤ treeCost) :
    Real.exp (lambda * (n : ℝ)) * Real.exp (mDiam * diamCost) ≤
      Real.exp (aTree * treeCost) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr
    (tree_reserve_pays_incidence_and_leaves_diameter
      lambda aTree mDiam cp R treeCost diamCost n hn hlambda hgap hmDiam
      hscale hgeom hdiam)

#print axioms incidence_le_twice_nonroot
#print axioms pivot_incidence_charge_absorbed
#print axioms tree_reserve_pays_incidence_and_leaves_diameter
#print axioms exp_incidence_times_diameter_le_tree_reserve

end Millennium.YangMills.TreeReserveReplay
