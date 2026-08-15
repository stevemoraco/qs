import Mathlib

/-!
# RH B146 convex near-L1 moment firewalls

Finite real/rational algebra only.

This file formalizes the load-bearing exponent ledgers and the two hostile
fixed-exponent models used in the B146 square-Mertens audit.

It does **not** formalize rearrangements, Holder duality, real fractional powers,
primes, Mertens' theorem, Mellin transforms, Landau's theorem, BGST matrices,
or the Riemann hypothesis.
-/

namespace RHB146ConvexMomentFirewalls

/-- For the conjugate pair `p=(J+1)/J`, `q=J+1`, the dimension-loss exponent is
exactly `1/q`. -/
theorem conjugate_dimension_loss_ledger
    (J : ℚ) (hJ : J + 1 ≠ 0) :
    1 - J / (J + 1) = 1 / (J + 1) := by
  field_simp [hJ]
  ring

/-- The near-one displacement of `p=(J+1)/J` is exactly `1/J`. -/
theorem near_one_exponent_ledger
    (J : ℚ) (hJ : J ≠ 0) :
    (J + 1) / J - 1 = 1 / J := by
  field_simp [hJ]
  ring

/-- Fixed exponent below one is generically too strong, not too weak.
Think of `t^2` equal depths `1/t^2`: total/weak-L1 depth is one, while the
square-root moment is `t`. -/
theorem fixed_half_moment_too_strong
    (t : ℝ) (ht : t ≠ 0) :
    t ^ 2 * (1 / t ^ 2) = 1 ∧
    t ^ 2 * (1 / t) = t := by
  constructor
  · field_simp [ht]
  · field_simp [ht]

/-- Fixed exponent above one is generically too weak.
Think of `t^2` equal depths `1/t`: the quadratic moment is one, while the
weak-L1 depth is `t`. -/
theorem fixed_two_moment_too_weak
    (t : ℝ) (ht : t ≠ 0) :
    t ^ 2 * (1 / t) ^ 2 = 1 ∧
    t ^ 2 * (1 / t) = t := by
  constructor
  · field_simp [ht]
  · field_simp [ht]

/-- Congruence preserves the sign of a one-dimensional negative direction but
can rescale every positive depth moment arbitrarily. -/
theorem one_dimensional_congruence_rescales_depth
    (R : ℝ) :
    R * (-1) * R = -(R ^ 2) := by
  ring

/-- The scalar threshold shift of a diagonal entry records exceedance exactly. -/
theorem shifted_negative_iff_depth_exceeds
    (x lambda : ℝ) :
    x + lambda < 0 ↔ -x > lambda := by
  linarith

#print axioms conjugate_dimension_loss_ledger
#print axioms near_one_exponent_ledger
#print axioms fixed_half_moment_too_strong
#print axioms fixed_two_moment_too_weak
#print axioms one_dimensional_congruence_rescales_depth
#print axioms shifted_negative_iff_depth_exceeds

end RHB146ConvexMomentFirewalls
