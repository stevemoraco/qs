import Mathlib

/-!
# RH B142 continuous Mertens L2 finite core

Finite real algebra only.

Between prime events the normalized ordinary-prime Mertens state is translated by
a nonnegative drift.  The human B142 reduction compares the left-endpoint
negative depth with the continuously drifting negative depth.  These declarations
formalize only that deterministic scalar geometry.

No primes, integration, logarithms, Mertens theorem, cubic gap theorem, zeta
function, or Riemann hypothesis is formalized here.
-/

namespace RHB142ContinuousMertensL2Finite

theorem negative_depth_monotone_under_downward_drift
    (m ell : ℝ) (hell : 0 ≤ ell) :
    max (-m) 0 ≤ max (-(m - ell)) 0 := by
  apply max_le
  · exact le_max_of_le_left (by linarith)
  · exact le_max_right _ _

theorem negative_depth_le_endpoint_depth_add_drift
    (m ell : ℝ) (hell : 0 ≤ ell) :
    max (-(m - ell)) 0 ≤ max (-m) 0 + ell := by
  apply max_le
  · have hneg : -m ≤ max (-m) 0 := le_max_left _ _
    linarith
  · exact add_nonneg (le_max_right _ _) hell

theorem add_sq_le_two_sq_add_two_sq (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem negative_depth_sq_sandwich
    (m ell : ℝ) (hell : 0 ≤ ell) :
    (max (-m) 0) ^ 2 ≤ (max (-(m - ell)) 0) ^ 2 ∧
    (max (-(m - ell)) 0) ^ 2 ≤
      2 * (max (-m) 0) ^ 2 + 2 * ell ^ 2 := by
  have hbase0 : 0 ≤ max (-m) 0 := le_max_right _ _
  have hdrift0 : 0 ≤ max (-(m - ell)) 0 := le_max_right _ _
  have hlow := negative_depth_monotone_under_downward_drift m ell hell
  have hupp := negative_depth_le_endpoint_depth_add_drift m ell hell
  constructor
  · nlinarith
  · have hs := add_sq_le_two_sq_add_two_sq (max (-m) 0) ell
    nlinarith

theorem drift_sq_le_bound_sq
    (ell b : ℝ) (hell : 0 ≤ ell) (hb : ell ≤ b) :
    ell ^ 2 ≤ b ^ 2 := by
  have hb0 : 0 ≤ b := hell.trans hb
  nlinarith

#print axioms negative_depth_monotone_under_downward_drift
#print axioms negative_depth_le_endpoint_depth_add_drift
#print axioms add_sq_le_two_sq_add_two_sq
#print axioms negative_depth_sq_sandwich
#print axioms drift_sq_le_bound_sq

end RHB142ContinuousMertensL2Finite
