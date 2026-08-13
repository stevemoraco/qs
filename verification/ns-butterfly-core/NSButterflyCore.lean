import Mathlib

namespace NSButterflyCore

theorem total_energy_derivative_zero
    {a b c aa bb cc lone ltwo x y z u v dx dy dz du dv : Real}
    (ha : a = b + c)
    (haa : aa = bb + cc)
    (hx : dx = -a * lone * y * z)
    (hy : dy = b * lone * x * z)
    (hz : dz = c * lone * x * y - aa * ltwo * u * v)
    (hu : du = bb * ltwo * z * v)
    (hv : dv = cc * ltwo * z * u) :
    2 * x * dx + 2 * y * dy + 2 * z * dz + 2 * u * du + 2 * v * dv = 0 := by
  rw [hx, hy, hz, hu, hv, ha, haa]
  ring

theorem upstream_action_derivative_zero
    {a b l x y z dx dy : Real}
    (hx : dx = -a * l * y * z)
    (hy : dy = b * l * x * z) :
    2 * b * x * dx + 2 * a * y * dy = 0 := by
  rw [hx, hy]
  ring

theorem downstream_action_derivative_zero
    {b c l z u v du dv : Real}
    (hu : du = b * l * z * v)
    (hv : dv = c * l * z * u) :
    2 * c * u * du - 2 * b * v * dv = 0 := by
  rw [hu, hv]
  ring

theorem bridge_u_action_derivative_zero
    {a c aa bb lone ltwo x y z u v dx dz du : Real}
    (hx : dx = -a * lone * y * z)
    (hz : dz = c * lone * x * y - aa * ltwo * u * v)
    (hu : du = bb * ltwo * z * v) :
    2 * (bb * c) * x * dx + 2 * (a * bb) * z * dz + 2 * (a * aa) * u * du = 0 := by
  rw [hx, hz, hu]
  ring

theorem bridge_v_action_derivative_zero
    {a c aa cc lone ltwo x y z u v dx dz dv : Real}
    (hx : dx = -a * lone * y * z)
    (hz : dz = c * lone * x * y - aa * ltwo * u * v)
    (hv : dv = cc * ltwo * z * u) :
    2 * (cc * c) * x * dx + 2 * (a * cc) * z * dz + 2 * (a * aa) * v * dv = 0 := by
  rw [hx, hz, hv]
  ring

theorem zero_downstream_seed_has_zero_tangent
    {b c l z u v du dv : Real}
    (huz : u = 0)
    (hvz : v = 0)
    (hu : du = b * l * z * v)
    (hv : dv = c * l * z * u) :
    And (du = 0) (dv = 0) := by
  subst u
  subst v
  simp_all

theorem shared_mode_zero_is_transverse
    {c aa lone ltwo x y u v dz : Real}
    (hz : dz = c * lone * x * y - aa * ltwo * u * v)
    (hne : c * lone * x * y != aa * ltwo * u * v) :
    dz != 0 := by
  rw [hz]
  exact sub_ne_zero.mpr hne

theorem upstream_pair_weighted_floor
    {a b x y r : Real}
    (hab : b <= a)
    (hact : b * x ^ 2 + a * y ^ 2 = b * r ^ 2) :
    b * r ^ 2 <= a * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg x]

theorem three_four_five_old_pair_floor
    {x y r : Real}
    (hact : x ^ 2 + 8 * y ^ 2 = r ^ 2) :
    r ^ 2 <= 8 * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg x]

#print axioms total_energy_derivative_zero
#print axioms upstream_action_derivative_zero
#print axioms downstream_action_derivative_zero
#print axioms bridge_u_action_derivative_zero
#print axioms bridge_v_action_derivative_zero
#print axioms zero_downstream_seed_has_zero_tangent
#print axioms shared_mode_zero_is_transverse
#print axioms upstream_pair_weighted_floor
#print axioms three_four_five_old_pair_floor

end NSButterflyCore
