import Mathlib

/-!
# C297 — weighted slice identification firewall

Finite scalar algebra for one load-bearing point in the Faizal–Shabir OS-transfer audit.

If an OS/slice form has the scalar shape

  <x,y>_OS = t * x * y,

with `0 < t < 1`, then the bare identity map into ordinary Euclidean `L2` is not an
isometry. The square-root weighted map `x ↦ sqrt(t) * x` is.

This file does not formalize Osterwalder–Schrader reconstruction, transfer operators,
Yang–Mills theory, the mass gap, or the Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirWeightedSliceIdentificationFirewall

/-- At the explicit contraction weight `t = 1/2`, the weighted OS norm of `1`
is not the ordinary Euclidean norm of `1`. -/
theorem bare_identity_not_isometry_at_half :
    ((1 / 2 : ℝ) * (1 : ℝ)^2) ≠ (1 : ℝ)^2 := by
  norm_num

/-- More generally, for a strict scalar contraction weight, the weighted norm
of a nonzero vector cannot equal its ordinary Euclidean norm. -/
theorem bare_identity_not_isometry
    (t x : ℝ)
    (ht0 : 0 ≤ t)
    (ht1 : t < 1)
    (hx : x ≠ 0) :
    t * x^2 ≠ x^2 := by
  intro h
  have hx2 : 0 < x^2 := sq_pos_of_ne_zero hx
  have hfactor : (1 - t) * x^2 = 0 := by
    nlinarith
  have h1t : 0 < 1 - t := by linarith
  nlinarith

/-- The square-root weighted scalar map is exactly isometric for the weighted
form. This is the scalar shadow of `[f] ↦ T^(1/2) f` for a positive operator
weighted Hilbert form. -/
theorem sqrt_weighted_map_isometry
    (t x : ℝ)
    (ht : 0 ≤ t) :
    (Real.sqrt t * x)^2 = t * x^2 := by
  rw [mul_pow]
  rw [Real.sq_sqrt ht]

#print axioms bare_identity_not_isometry_at_half
#print axioms bare_identity_not_isometry
#print axioms sqrt_weighted_map_isometry

end Millennium.YangMills.FaizalShabirWeightedSliceIdentificationFirewall
