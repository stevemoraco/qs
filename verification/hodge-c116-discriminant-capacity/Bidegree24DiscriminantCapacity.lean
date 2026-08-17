import Mathlib

/-!
# Hodge C116 quartic-discriminant capacity: finite arithmetic core

This file formalizes only the integer inequality used after the geometric
normalization/discriminant theorem has supplied the residual fibre degree

`8*r^2 + 4*r - 2 - m*(4*r+1)`

and the branch-multiplicity lower bound `m >= 2*r+2`.

It does not formalize K3 surfaces, finite covers, normalization, conductor
lengths, trace discriminants, Casnati--Ekedahl geometry, Hodge theory, or a
Clay theorem.
-/

namespace Millennium.Hodge.Bidegree24DiscriminantCapacity

/-- Exact decomposition of the residual quartic-discriminant fibre degree
around the smallest branch multiplicity allowed by C115. -/
theorem residual_fibre_degree_identity (r m : ℤ) :
    8 * r ^ 2 + 4 * r - 2 - m * (4 * r + 1) =
      -6 * r - 4 - (m - (2 * r + 2)) * (4 * r + 1) := by
  ring

/-- Once `r >= 1` and the branch multiplicity is at least `2r+2`, the
residual discriminant class has strictly negative fibre degree. -/
theorem residual_fibre_degree_negative (r m : ℤ)
    (hr : 1 ≤ r) (hm : 2 * r + 2 ≤ m) :
    8 * r ^ 2 + 4 * r - 2 - m * (4 * r + 1) < 0 := by
  rw [residual_fibre_degree_identity]
  have hgap : 0 ≤ m - (2 * r + 2) := by
    omega
  have hfactor : 0 ≤ 4 * r + 1 := by
    omega
  have hprod : 0 ≤ (m - (2 * r + 2)) * (4 * r + 1) :=
    mul_nonneg hgap hfactor
  nlinarith

/-- A class with the displayed residual fibre degree cannot simultaneously
have nonnegative intersection with the nef fibre. -/
theorem no_nonnegative_residual_fibre_degree (r m : ℤ)
    (hr : 1 ≤ r) (hm : 2 * r + 2 ≤ m)
    (heffective : 0 ≤ 8 * r ^ 2 + 4 * r - 2 - m * (4 * r + 1)) : False := by
  exact (not_lt_of_ge heffective) (residual_fibre_degree_negative r m hr hm)

#print axioms residual_fibre_degree_identity
#print axioms residual_fibre_degree_negative
#print axioms no_nonnegative_residual_fibre_degree

end Millennium.Hodge.Bidegree24DiscriminantCapacity
