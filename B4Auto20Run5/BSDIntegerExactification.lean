import Mathlib

namespace B4Auto20Run5

/-- BANKER: an integer-valued defect has a unit spectral gap away from zero.
Any strict bound `|z| < 1` therefore exactifies the defect to `z = 0`. This is
the finite arithmetic core by which asymptotic/analytic control can become an
exact BSD identity, but only after integrality has been proved. -/
theorem bsd_integer_defect_abs_lt_one_exactifies
    (z : ℤ) (hsmall : |z| < 1) :
    z = 0 := by
  omega

/-- CLEANER: equivalently, every nonzero integer defect has magnitude at least
one. Thus a proof may target a strict unit error bound once the relevant defect
has independently been shown to lie in `ℤ`. -/
theorem bsd_nonzero_integer_defect_has_unit_gap
    (z : ℤ) (hz : z ≠ 0) :
    1 ≤ |z| := by
  omega

/-- CRITIC: the strict inequality is load-bearing. A non-strict unit bound can
still hide the nonzero defect `z = 1`, so `|z| ≤ 1` is not an exactification
criterion. -/
theorem bsd_nonstrict_unit_bound_does_not_exactify :
    |(1 : ℤ)| ≤ 1 ∧ (1 : ℤ) ≠ 0 := by
  norm_num

#print axioms B4Auto20Run5.bsd_integer_defect_abs_lt_one_exactifies
#print axioms B4Auto20Run5.bsd_nonzero_integer_defect_has_unit_gap
#print axioms B4Auto20Run5.bsd_nonstrict_unit_bound_does_not_exactify

end B4Auto20Run5
