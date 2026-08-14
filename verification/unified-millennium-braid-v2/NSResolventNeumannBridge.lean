import Mathlib

namespace Millennium.NavierStokes.Resolvent

theorem isUnit_sub_of_mul_inv_norm_lt_one
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    (a : Rˣ) (e : R)
    (h : ‖e * (↑a⁻¹ : R)‖ < 1) :
    IsUnit ((↑a : R) - e) := by
  have hsmall : IsUnit ((1 : R) - e * (↑a⁻¹ : R)) :=
    isUnit_one_sub_of_norm_lt_one h
  have hprod : IsUnit (((1 : R) - e * (↑a⁻¹ : R)) * (↑a : R)) :=
    hsmall.mul a.isUnit
  simpa [sub_mul, mul_assoc] using hprod

theorem isUnit_add_of_mul_inv_norm_lt_one
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    (a : Rˣ) (e : R)
    (h : ‖e * (↑a⁻¹ : R)‖ < 1) :
    IsUnit ((↑a : R) + e) := by
  have hneg : ‖(-e) * (↑a⁻¹ : R)‖ < 1 := by
    simpa using h
  simpa using isUnit_sub_of_mul_inv_norm_lt_one a (-e) hneg

theorem contour_units_persist
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    {ι : Type*}
    (a : ι → Rˣ) (e : ι → R)
    (h : ∀ z, ‖e z * (↑(a z)⁻¹ : R)‖ < 1) :
    ∀ z, IsUnit ((↑(a z) : R) - e z) := by
  intro z
  exact isUnit_sub_of_mul_inv_norm_lt_one (a z) (e z) (h z)

#print axioms isUnit_sub_of_mul_inv_norm_lt_one
#print axioms isUnit_add_of_mul_inv_norm_lt_one
#print axioms contour_units_persist

end Millennium.NavierStokes.Resolvent
