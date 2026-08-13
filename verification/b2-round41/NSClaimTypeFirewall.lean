import Mathlib

/-!
# Navier--Stokes claimed-proof type firewall

This file formalizes only two finite algebraic cores from the hostile audit:
(1) simultaneous scaled 3D and 5D divergence equations force the radial
component to vanish, and (2) modes 451 through 1199 are outside both a
450-mode finite block and a tail theorem beginning at 1200.  It does not
formalize cylindrical differential geometry, interval arithmetic,
Newton--Kantorovich, Navier--Stokes solutions, or the Clay problem.
-/

namespace MillenniumBraid
namespace B2Round41NSClaim

/-- After multiplication by a positive radius, physical 3D incompressibility
has coefficient one on the radial velocity, whereas the auxiliary 5D law has
coefficient three.  Simultaneous validity forces the radial component to
vanish. -/
theorem threeD_and_fiveD_divergence_force_radial_zero
    {r common radial : ℝ}
    (h3 : r * common + radial = 0)
    (h5 : r * common + 3 * radial = 0) :
    radial = 0 := by
  linarith

/-- A field satisfying the scaled 5D weighted-divergence equation has scaled
physical 3D divergence equal to `-2 * radial`. -/
theorem fiveD_law_physical_residual
    {r common radial : ℝ}
    (h5 : r * common + 3 * radial = 0) :
    r * common + radial = -2 * radial := by
  linarith

/-- If the same nonzero radial component were physically divergence-free and
5D-weighted divergence-free, contradiction follows. -/
theorem nonzero_radial_cannot_satisfy_both
    {r common radial : ℝ}
    (hradial : radial ≠ 0)
    (h3 : r * common + radial = 0)
    (h5 : r * common + 3 * radial = 0) : False := by
  exact hradial (threeD_and_fiveD_divergence_force_radial_zero h3 h5)

/-- The first uncovered integer mode lies strictly above the finite cutoff and
strictly below the advertised tail threshold. -/
theorem mode451_is_uncovered :
    (450 : ℕ) < 451 ∧ 451 < 1200 := by
  norm_num

/-- The entire displayed middle annulus is disjoint from the two certified
index domains `j ≤ 450` and `1200 ≤ j`. -/
theorem middle_mode_outside_both_certificates
    {j : ℕ} (hlo : 451 ≤ j) (hhi : j ≤ 1199) :
    ¬ (j ≤ 450 ∨ 1200 ≤ j) := by
  omega

/-- A tail statement whose hypothesis begins at 1200 cannot be instantiated at
mode 451. -/
theorem tail_hypothesis_not_available_at_451 :
    ¬ (1200 : ℕ) ≤ 451 := by
  norm_num

#print axioms threeD_and_fiveD_divergence_force_radial_zero
#print axioms fiveD_law_physical_residual
#print axioms nonzero_radial_cannot_satisfy_both
#print axioms mode451_is_uncovered
#print axioms middle_mode_outside_both_certificates
#print axioms tail_hypothesis_not_available_at_451

end B2Round41NSClaim
end MillenniumBraid
