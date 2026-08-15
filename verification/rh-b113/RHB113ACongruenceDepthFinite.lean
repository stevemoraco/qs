import Mathlib

/-!
# RH B113A congruence-depth finite firewall

Finite scalar algebra only.

Congruence preserves the sign of a one-dimensional negative form but can scale
its depth arbitrarily.  Carrying a positive metric simultaneously removes this
artificial scaling at the generalized-eigenvalue level.

This file does not formalize Hermitian matrix inertia, contour Hankel matrices,
primes, zeta, or RH.
-/

namespace RHB113ACongruenceDepthFinite

/-- A one-dimensional negative form stays negative under a nonzero scalar
congruence, while its absolute depth becomes `R^2`. -/
theorem scalar_negative_congruence_depth
    {R : ℝ} (hR : R ≠ 0) :
    -(R ^ 2) < 0 ∧ max (R ^ 2) 0 = R ^ 2 := by
  have hsq : 0 < R ^ 2 := sq_pos_of_ne_zero hR
  constructor
  · linarith
  · exact max_eq_left hsq.le

/-- The congruence depth can exceed any prescribed nonnegative budget while the
sign remains negative. -/
theorem scalar_congruence_depth_unbounded
    {K : ℝ} (hK : 0 ≤ K) :
    let R : ℝ := K + 1
    -(R ^ 2) < 0 ∧ K < R ^ 2 := by
  dsimp
  constructor
  · have hR : 0 < K + 1 := by linarith
    nlinarith
  · nlinarith

/-- Simultaneously scaling a scalar Hermitian form and its positive metric leaves
the generalized eigenvalue ratio unchanged. -/
theorem scalar_metric_normalized_congruence_invariant
    {a g s : ℝ} (hg : g ≠ 0) (hs : s ≠ 0) :
    (s ^ 2 * a) / (s ^ 2 * g) = a / g := by
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  field_simp [hs2, hg]

/-- If the metric is not co-scaled, the same congruence multiplies the scalar
Rayleigh value by `s^2`; this is the exact normalization firewall. -/
theorem scalar_unscaled_metric_changes_depth
    (a s : ℝ) :
    s ^ 2 * a - a = (s ^ 2 - 1) * a := by
  ring

#print axioms scalar_negative_congruence_depth
#print axioms scalar_congruence_depth_unbounded
#print axioms scalar_metric_normalized_congruence_invariant
#print axioms scalar_unscaled_metric_changes_depth

end RHB113ACongruenceDepthFinite
