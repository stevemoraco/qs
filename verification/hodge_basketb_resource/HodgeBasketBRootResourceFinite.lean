import Mathlib

namespace HodgeBasketBRootResourceFinite

/-- If a stationary-nonnormal root has normalization parameter `k`, the root
zero-chain charge `k ≤ h+1` and the nonmoving residual budget can supply at
most twelve units of alpha degree, never thirteen. -/
theorem stationary_nonnormal_without_moving_impossible
    (h k residual : Nat)
    (hh : h ≤ 5)
    (hk : k ≤ h + 1)
    (htotal : 2 * k + residual = 13)
    (hresidual : residual ≤ 2 * (5 - h)) :
    False := by
  omega

/-- A root stationary-nonnormal contact needs at least one root unit point,
while an off-root moving `A3` needs at least four. If all five unit points are
partitioned among root, moving, and residual clusters, the allocation is forced. -/
theorem root_and_moving_allocation_unique
    (h c r : Nat)
    (hsum : h + c + r = 5)
    (hh : 1 ≤ h)
    (hc : 4 ≤ c) :
    h = 1 ∧ c = 4 ∧ r = 0 := by
  omega

/-- After the forced `h=1` allocation, the normalization chain bound and
`k≥2` exactify the root stationary-nonnormal order to four and the remaining
moving alpha order to nine. -/
theorem mixed_pattern_is_four_plus_nine
    (h k rootOrder movingOrder : Nat)
    (hh : h = 1)
    (hkLower : 2 ≤ k)
    (hkUpper : k ≤ h + 1)
    (hroot : rootOrder = 2 * k)
    (htotal : rootOrder + movingOrder = 13) :
    k = 2 ∧ rootOrder = 4 ∧ movingOrder = 9 := by
  omega

/-- Three root zero curves and four off-root zero-curve resources cannot both
be charged to a basket containing only five unit points. -/
theorem root_moving_excludes_offroot_moving
    (h c : Nat)
    (hroot : 3 ≤ h)
    (hoffroot : 4 ≤ c)
    (hbudget : h + c ≤ 5) :
    False := by
  omega

/-- If the root moving contact has alpha order `M` and every remaining
nonmoving unit point contributes at most two, then `M ≥ 2h+3`. -/
theorem root_moving_order_lower_bound
    (h M residual : Nat)
    (hh : h ≤ 5)
    (htotal : M + residual = 13)
    (hresidual : residual ≤ 2 * (5 - h)) :
    2 * h + 3 ≤ M := by
  omega

/-- The three possible root-unit counts give the explicit lower windows used
by the geometric reduction. -/
theorem root_moving_windows
    (h M residual : Nat)
    (hh : h = 3 ∨ h = 4 ∨ h = 5)
    (htotal : M + residual = 13)
    (hresidual : residual ≤ 2 * (5 - h)) :
    (h = 3 → 9 ≤ M) ∧
    (h = 4 → 11 ≤ M) ∧
    (h = 5 → M = 13) := by
  rcases hh with rfl | rfl | rfl <;> omega

#print axioms HodgeBasketBRootResourceFinite.stationary_nonnormal_without_moving_impossible
#print axioms HodgeBasketBRootResourceFinite.root_and_moving_allocation_unique
#print axioms HodgeBasketBRootResourceFinite.mixed_pattern_is_four_plus_nine
#print axioms HodgeBasketBRootResourceFinite.root_moving_excludes_offroot_moving
#print axioms HodgeBasketBRootResourceFinite.root_moving_order_lower_bound
#print axioms HodgeBasketBRootResourceFinite.root_moving_windows

end HodgeBasketBRootResourceFinite
