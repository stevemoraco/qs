import Mathlib

namespace Millennium.PNP.LowSupportGirthInjectivityFirewall

theorem low_support_boundary_collision_impossible
    (a b s girth cycleLen : ℕ)
    (ha : a ≤ s)
    (hb : b ≤ s)
    (hgirth : girth ≤ cycleLen)
    (hshort : cycleLen ≤ a + b)
    (hgt : 2 * s < girth) : False := by
  omega

theorem two_supports_fit_twice_radius
    (a b s : ℕ)
    (ha : a ≤ s)
    (hb : b ≤ s) :
    a + b ≤ 2 * s := by
  omega

theorem collision_forces_girth_le_twice_support
    (a b s girth cycleLen : ℕ)
    (ha : a ≤ s)
    (hb : b ≤ s)
    (hgirth : girth ≤ cycleLen)
    (hshort : cycleLen ≤ a + b) :
    girth ≤ 2 * s := by
  omega

theorem strict_girth_margin_rejects_collision_certificate
    (s girth cycleLen supportUnion : ℕ)
    (hmargin : 2 * s < girth)
    (hcycle : girth ≤ cycleLen)
    (hcycleSupport : cycleLen ≤ supportUnion)
    (hunion : supportUnion ≤ 2 * s) : False := by
  omega

#print axioms low_support_boundary_collision_impossible
#print axioms two_supports_fit_twice_radius
#print axioms collision_forces_girth_le_twice_support
#print axioms strict_girth_margin_rejects_collision_certificate

end Millennium.PNP.LowSupportGirthInjectivityFirewall
