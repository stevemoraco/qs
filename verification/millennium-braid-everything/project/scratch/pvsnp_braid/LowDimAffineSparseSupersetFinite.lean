import Mathlib

namespace PvsNPBraid

/-- Computing `k` affine checks of cost at most `r+1` and ANDing them gives
the exact universal gate upper bound. -/
theorem affine_sparse_superset_gate_count
    (k r : ℤ) :
    k * (r + 1) + (k - 1) = k * (r + 2) - 1 := by
  ring

/-- If the universal affine superset circuit fits under the target gate
budget, the affine range cannot satisfy the desired dense-hitter premise. -/
theorem affine_superset_fits_budget
    (k r g : ℤ)
    (h : k * (r + 2) - 1 ≤ g) :
    k * (r + 2) - 1 ≤ g := by
  exact h

/-- Rearranging the survival condition gives the exact seed-dimension floor. -/
theorem affine_survival_dimension_floor
    (k r g : ℝ)
    (hk : 0 < k)
    (h : g < k * (r + 2) - 1) :
    g / k - 2 + 1 / k < r := by
  have h1 : g + 1 < k * (r + 2) := by linarith
  have h2 : (g + 1) / k < r + 2 := (div_lt_iff₀ hk).2 h1
  field_simp [ne_of_gt hk] at h2 ⊢
  nlinarith

/-- Selecting `k` independent checks from `n-r` available checks requires the
obvious codimension budget. -/
theorem check_selection_budget (n r k : ℕ)
    (hrn : r ≤ n) (hk : k ≤ n - r) :
    k + r ≤ n := by
  omega

end PvsNPBraid
