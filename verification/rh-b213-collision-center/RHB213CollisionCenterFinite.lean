import Mathlib

/-!
# RH B213 collision-centre dichotomy — finite algebra only

This public verification mirror contains only the real polynomial facts used in
RH B212/B213's rational-centre isolation argument. It does not formalize Xi,
zeta zeros, contour integration, Deng--Yang--Lu, B46, RH, not-RH, or the global
zero-set isolation theorem.
-/

namespace RHB213CollisionCenterFinite

/-- When real coordinates differ, two equal-distance collision equations have
at most one real centre. -/
theorem equal_distance_collision_center_unique
    {x y gamma delta c₁ c₂ : ℝ}
    (hx : x ≠ gamma)
    (h₁ : x ^ 2 + y ^ 2 - gamma ^ 2 - delta ^ 2
      - 2 * c₁ * (x - gamma) = 0)
    (h₂ : x ^ 2 + y ^ 2 - gamma ^ 2 - delta ^ 2
      - 2 * c₂ * (x - gamma) = 0) :
    c₁ = c₂ := by
  have hprod : (c₁ - c₂) * (x - gamma) = 0 := by
    nlinarith [h₁, h₂]
  rcases mul_eq_zero.mp hprod with hc | hxzero
  · linarith
  · exact False.elim (hx (sub_eq_zero.mp hxzero))

/-- If two nodes have the same real coordinate and are equidistant from one
real centre, then their squared transverse coordinates agree. -/
theorem equal_distance_same_real_forces_squared_transverse_match
    {x y gamma delta c : ℝ}
    (hx : x = gamma)
    (h : x ^ 2 + y ^ 2 - gamma ^ 2 - delta ^ 2
      - 2 * c * (x - gamma) = 0) :
    y ^ 2 = delta ^ 2 := by
  subst gamma
  nlinarith [h]

/-- For a genuinely different conjugate pair, expressed modulo conjugation by
`x ≠ gamma ∨ y^2 ≠ delta^2`, two collision centres must coincide. Thus such a
competitor excludes at most one real centre. -/
theorem distinct_conjugate_pair_collision_center_at_most_one
    {x y gamma delta c₁ c₂ : ℝ}
    (hdist : x ≠ gamma ∨ y ^ 2 ≠ delta ^ 2)
    (h₁ : x ^ 2 + y ^ 2 - gamma ^ 2 - delta ^ 2
      - 2 * c₁ * (x - gamma) = 0)
    (h₂ : x ^ 2 + y ^ 2 - gamma ^ 2 - delta ^ 2
      - 2 * c₂ * (x - gamma) = 0) :
    c₁ = c₂ := by
  rcases hdist with hx | htrans
  · exact equal_distance_collision_center_unique hx h₁ h₂
  · by_cases hx : x = gamma
    · have hsquare : y ^ 2 = delta ^ 2 :=
        equal_distance_same_real_forces_squared_transverse_match hx h₁
      exact False.elim (htrans hsquare)
    · exact equal_distance_collision_center_unique hx h₁ h₂

#print axioms equal_distance_collision_center_unique
#print axioms equal_distance_same_real_forces_squared_transverse_match
#print axioms distinct_conjugate_pair_collision_center_at_most_one

end RHB213CollisionCenterFinite
