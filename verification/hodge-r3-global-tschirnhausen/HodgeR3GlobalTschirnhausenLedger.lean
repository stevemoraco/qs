import Mathlib

/-!
Finite arithmetic companion to the global r=3 Tschirnhausen/basepoint ledger.

This file proves only integer degree/Chern-number identities and the resulting
four-case enumeration.  It does not formalize triple covers, Tschirnhausen
bundles, finite-flatness, singularity corrections, K3 surfaces, algebraic
cycles, Hodge structures, or the Hodge conjecture.
-/

namespace Millennium.Hodge.R3GlobalTschirnhausenLedger

/-- A projective degree-13 square-form family contributes degree 26 to each
quadratic cubic coefficient and degree 104 to the full cubic discriminant. -/
theorem full_discriminant_parameter_degree :
    2 * (13 : ℤ) + 6 * 13 = 4 * (2 * 13) := by
  norm_num

/-- The residual discriminant `Phi` has parameter degree 78; restoring the
boundary factor `alpha^2` contributes the missing 26 degrees. -/
theorem alpha_boundary_degree_correction :
    2 * (13 : ℤ) + 78 = 104 := by
  norm_num

/-- The fixed target-base conductor/branch degree ledger. -/
theorem target_base_degree_ledger :
    2 * (9 : ℤ) + 6 = 24 := by
  norm_num

/-- Miranda's smooth triple-cover K^2 expression simplifies to `6-2a` for
`c1(E)=(-a,-3)` and `c2(E)=2a-2` on `P1 x P1`. -/
theorem miranda_k2_ledger (a : ℤ) :
    3 * 8 - 4 * (2 * a + 6) + 2 * (6 * a) - 3 * (2 * a - 2)
      = 6 - 2 * a := by
  ring

/-- Full discriminant = index-square times normalized branch, in parameter
numerical degrees. -/
theorem full_index_branch_degree_ledger (a : ℤ) :
    2 * (52 - a) + 2 * a = 104 := by
  ring

/-- After a justified degree-13 alpha cancellation, the residual degree ledger
is `2(39-a)+2a=78`. -/
theorem residual_index_branch_degree_ledger (a : ℤ) :
    2 * (39 - a) + 2 * a = 78 := by
  ring

/-- Nonvanishing of both extremal binary-cubic coefficients forces the
horizontal Tschirnhausen parameter into the interval `3 <= a <= 6`. -/
theorem extremal_nonvanishing_bounds (a : ℤ)
    (hleading : 0 ≤ 2 * a - 6)
    (htrailing : 0 ≤ 6 - a) :
    3 ≤ a ∧ a ≤ 6 := by
  omega

/-- In the smooth finite model, `N=2a-6` together with the two extremal
nonvanishing inequalities leaves exactly four basepoint counts. -/
theorem smooth_model_four_cases (a N : ℤ)
    (hN : N = 2 * a - 6)
    (hleading : 0 ≤ 2 * a - 6)
    (htrailing : 0 ≤ 6 - a) :
    (a = 3 ∧ N = 0) ∨
    (a = 4 ∧ N = 2) ∨
    (a = 5 ∧ N = 4) ∨
    (a = 6 ∧ N = 6) := by
  omega

/-- The four normalized branch parameter degrees are exactly 6,8,10,12. -/
theorem branch_degree_four_cases (a : ℤ)
    (ha : a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6) :
    2 * a = 6 ∨ 2 * a = 8 ∨ 2 * a = 10 ∨ 2 * a = 12 := by
  omega

/-- After alpha cancellation, the four residual conductor parameter degrees
are exactly 36,35,34,33. -/
theorem residual_conductor_degree_four_cases (a : ℤ)
    (ha : a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6) :
    39 - a = 36 ∨ 39 - a = 35 ∨ 39 - a = 34 ∨ 39 - a = 33 := by
  omega

#print axioms full_discriminant_parameter_degree
#print axioms alpha_boundary_degree_correction
#print axioms target_base_degree_ledger
#print axioms miranda_k2_ledger
#print axioms full_index_branch_degree_ledger
#print axioms residual_index_branch_degree_ledger
#print axioms extremal_nonvanishing_bounds
#print axioms smooth_model_four_cases
#print axioms branch_degree_four_cases
#print axioms residual_conductor_degree_four_cases

end Millennium.Hodge.R3GlobalTschirnhausenLedger
