import Mathlib

namespace Millennium.Hodge.Bidegree24QuadraticConductorParity

theorem branch_multiplicity_lower_bound (r m : ℤ)
    (hintersection : 0 ≤ -4 * r - 4 + 2 * m) :
    2 * r + 2 ≤ m := by
  omega

theorem forced_branch_is_multiple (r m : ℤ)
    (hr : 1 ≤ r) (hintersection : 0 ≤ -4 * r - 4 + 2 * m) :
    4 ≤ m := by
  have hm := branch_multiplicity_lower_bound r m hintersection
  omega

theorem first_coordinate_not_even (x : ℤ) :
    1 ≠ 2 * x := by
  omega

theorem correspondence_column_not_double (r x y : ℤ) :
    ¬ (1 = 2 * x ∧ 4 * r + 1 = 2 * y) := by
  intro h
  exact first_coordinate_not_even x h.1

theorem conductor_descent_parity_contradiction (r m x y : ℤ)
    (hr : 1 ≤ r)
    (hintersection : 0 ≤ -4 * r - 4 + 2 * m)
    (hevenCycle : 1 = 2 * x ∧ 4 * r + 1 = 2 * y) : False := by
  have _hmultiple : 4 ≤ m := forced_branch_is_multiple r m hr hintersection
  exact correspondence_column_not_double r x y hevenCycle

#print axioms branch_multiplicity_lower_bound
#print axioms forced_branch_is_multiple
#print axioms first_coordinate_not_even
#print axioms correspondence_column_not_double
#print axioms conductor_descent_parity_contradiction

end Millennium.Hodge.Bidegree24QuadraticConductorParity
