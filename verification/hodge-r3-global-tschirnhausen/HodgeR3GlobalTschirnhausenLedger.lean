import Mathlib

/-!
Finite arithmetic companion to the global r=3 Tschirnhausen/basepoint ledger.

This file proves only integer degree/Chern-number identities and the resulting
four-case enumeration/contradiction.  It does not formalize triple covers,
Tschirnhausen bundles, finite-flatness, singularity corrections, K3 surfaces,
movable linear systems, basepoint multiplicities, algebraic cycles, Hodge
structures, or the Hodge conjecture.
-/

namespace Millennium.Hodge.R3GlobalTschirnhausenLedger

theorem full_discriminant_parameter_degree :
    2 * (13 : ℤ) + 6 * 13 = 4 * (2 * 13) := by
  norm_num

theorem alpha_boundary_degree_correction :
    2 * (13 : ℤ) + 78 = 104 := by
  norm_num

theorem target_base_degree_ledger :
    2 * (9 : ℤ) + 6 = 24 := by
  norm_num

theorem miranda_k2_ledger (a : ℤ) :
    3 * 8 - 4 * (2 * a + 6) + 2 * (6 * a) - 3 * (2 * a - 2)
      = 6 - 2 * a := by
  ring

theorem full_index_branch_degree_ledger (a : ℤ) :
    2 * (52 - a) + 2 * a = 104 := by
  ring

theorem residual_index_branch_degree_ledger (a : ℤ) :
    2 * (39 - a) + 2 * a = 78 := by
  ring

theorem extremal_nonvanishing_bounds (a : ℤ)
    (hleading : 0 ≤ 2 * a - 6)
    (htrailing : 0 ≤ 6 - a) :
    3 ≤ a ∧ a ≤ 6 := by
  omega

theorem smooth_model_four_cases (a N : ℤ)
    (hN : N = 2 * a - 6)
    (hleading : 0 ≤ 2 * a - 6)
    (htrailing : 0 ≤ 6 - a) :
    (a = 3 ∧ N = 0) ∨
    (a = 4 ∧ N = 2) ∨
    (a = 5 ∧ N = 4) ∨
    (a = 6 ∧ N = 6) := by
  omega

theorem branch_degree_four_cases (a : ℤ)
    (ha : a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6) :
    2 * a = 6 ∨ 2 * a = 8 ∨ 2 * a = 10 ∨ 2 * a = 12 := by
  omega

theorem residual_conductor_degree_four_cases (a : ℤ)
    (ha : a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6) :
    39 - a = 36 ∨ 39 - a = 35 ∨ 39 - a = 34 ∨ 39 - a = 33 := by
  omega

theorem moving_pencil_requires_eighteen (b N : ℤ)
    (hb : 6 ≤ b)
    (hN : N = 6 * (b - 3)) :
    18 ≤ N := by
  omega

theorem smooth_triple_model_numerical_contradiction (a b N : ℤ)
    (hsmooth : N = 2 * a - 6)
    (hleading : 0 ≤ 2 * a - 6)
    (htrailing : 0 ≤ 6 - a)
    (hmoving : N = 6 * (b - 3))
    (hb : 6 ≤ b) :
    False := by
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
#print axioms moving_pencil_requires_eighteen
#print axioms smooth_triple_model_numerical_contradiction

end Millennium.Hodge.R3GlobalTschirnhausenLedger
