import Mathlib

noncomputable section

/-!
# Navier--Stokes: Yu affine-jet and fixed-filter radius firewalls

This finite file isolates two uncertainty-reducing facts from the current audit
of Runlong Yu's filtered far-field route (arXiv:2606.27560v1).

1. Corollary 2.3 carries the filter-ratio loss `(r / ell)^5`.  If one tries to
   swallow farther annuli merely by enlarging the physical near-field radius by
   a factor `s` while keeping the fine filter `ell` fixed, that loss grows like
   `s^5`, whereas the reassigned annular kernel gains only one inverse power.
   The net scalar factor is therefore `s^4`, not a small quantity.

2. Yu's fixed-annulus harmonic route isolates a recurrent affine strain jet.
   The explicit trace-free affine field `u=(x,-y,0)` is locally pressure-balanced
   by `p=-(x^2+y^2)/2`; viscosity sees no second derivatives, while the strain
   has a strictly positive stretching direction.  Thus incompressibility plus
   the local Navier--Stokes algebra cannot, by themselves, eliminate an affine
   external strain mode.  Any rigidity argument must use global finite-energy
   compatibility, recurrence/cancellation, or another genuinely nonlocal input.

The affine field has infinite global kinetic energy and is used only as a local
finite algebraic firewall.  Nothing here proves PDE realizability of Yu's
obstruction profile, regularity, or blow-up.
-/

namespace NSYuAffineJetRadiusTradeoff

/-- Enlarging the physical radius by `s` at fixed fine filter multiplies Yu's
`(r/ell)^5` loss by `s^5`.  Pairing that with only a one-power annular gain
leaves the exact net factor `s^4`. -/
theorem fixed_filter_radius_enlargement_net_factor
    {s : ℝ} (hs : s ≠ 0) :
    s ^ 5 * (1 / s) = s ^ 4 := by
  field_simp [hs]

/-- The dyadic version of the same tradeoff at one shell step: a factor `2^5`
from the fixed-filter near-field loss and a factor `1/2` from the annular kernel
leave a factor `16`. -/
theorem one_dyadic_shell_net_factor :
    (2 : ℝ) ^ 5 * (1 / 2 : ℝ) = 16 := by
  norm_num

/-- The explicit affine velocity `u=(x,-y,0)` is divergence free at the level
of its constant derivative matrix. -/
theorem affine_trace_free :
    (1 : ℝ) + (-1) + 0 = 0 := by
  norm_num

/-- First component of the steady affine Navier--Stokes balance.
For `u=(x,-y,0)`, `(u·∇)u_1=x`; for
`p=-(x^2+y^2)/2`, `∂_1 p=-x`. -/
theorem affine_first_component_pressure_balance (x y : ℝ) :
    x * 1 + (-y) * 0 + (-x) = 0 := by
  ring

/-- Second component of the same steady affine balance:
`(u·∇)u_2=y` and `∂_2 p=-y`. -/
theorem affine_second_component_pressure_balance (x y : ℝ) :
    x * 0 + (-y) * (-1) + (-y) = 0 := by
  ring

/-- The third component is identically zero. -/
theorem affine_third_component_pressure_balance :
    (0 : ℝ) = 0 := rfl

/-- The affine strain `diag(1,-1,0)` has a strictly positive stretching
direction: on the unit vector `e_1`, the quadratic stretching coefficient is
exactly one. -/
theorem affine_jet_has_positive_stretching_direction :
    (1 : ℝ) * 1 ^ 2 + (-1 : ℝ) * 0 ^ 2 + 0 * 0 ^ 2 = 1 := by
  norm_num

/-- One conjunction records the local no-free-lunch firewall: trace-free affine
strain, exact pressure balance, and positive stretching coexist. -/
theorem local_ns_algebra_does_not_kill_affine_strain (x y : ℝ) :
    ((1 : ℝ) + (-1) + 0 = 0) ∧
    (x * 1 + (-y) * 0 + (-x) = 0) ∧
    (x * 0 + (-y) * (-1) + (-y) = 0) ∧
    ((1 : ℝ) * 1 ^ 2 + (-1 : ℝ) * 0 ^ 2 + 0 * 0 ^ 2 = 1) := by
  exact ⟨affine_trace_free,
    affine_first_component_pressure_balance x y,
    affine_second_component_pressure_balance x y,
    affine_jet_has_positive_stretching_direction⟩

#print axioms fixed_filter_radius_enlargement_net_factor
#print axioms one_dyadic_shell_net_factor
#print axioms affine_trace_free
#print axioms affine_first_component_pressure_balance
#print axioms affine_second_component_pressure_balance
#print axioms affine_jet_has_positive_stretching_direction
#print axioms local_ns_algebra_does_not_kill_affine_strain

end NSYuAffineJetRadiusTradeoff
