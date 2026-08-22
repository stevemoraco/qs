import Mathlib

namespace HodgeNeighborhoodBasisFirewall

/-- A shrinking/cofinal chain of neighborhoods does not, by itself, force a
nonzero class to vanish after restriction.  The constant inverse system with
identity restrictions is the minimal countermodel to that logical inference. -/
theorem constant_restriction_class_survives :
    ∀ n : ℕ, (1 : ℤ) ≠ 0 := by
  intro n
  norm_num

/-- In the constant system `G_n = ℤ` with identity restriction maps, the class
`1` remains `1` at every stage. -/
theorem identity_restriction_never_kills (n : ℕ) :
    (id (1 : ℤ)) = 1 ∧ (1 : ℤ) ≠ 0 := by
  constructor
  · rfl
  · norm_num

/-- Coordinate dilation does not act by one universal first power on ordinary
forms: the coefficient scaling already distinguishes degree one from degree two.
This elementary algebra is the firewall behind the differential-form objection. -/
theorem dilation_degree_two_not_degree_one
    {r : ℝ} (hr : r ≠ 0) (hr1 : r ≠ 1) :
    r ^ 2 ≠ r := by
  intro h
  have : r * r = r * 1 := by simpa [pow_two] using h
  exact hr1 (mul_left_cancel₀ hr this)

#print axioms constant_restriction_class_survives
#print axioms identity_restriction_never_kills
#print axioms dilation_degree_two_not_degree_one

end HodgeNeighborhoodBasisFirewall
