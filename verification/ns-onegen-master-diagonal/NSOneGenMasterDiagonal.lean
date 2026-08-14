import Mathlib

/-!
# Navier--Stokes one-generation master diagonal

Finite exponent bookkeeping only.

This file formalizes the polynomial dominance used after freezing one AO mode:
with

* seed `delta = M^-1`,
* swirl-return radius `R = M^2`,
* axial-return radius `A = M`,
* packet window `B_p = M`,
* base window `B_0 = M^4`,
* normalized viscosity `epsilon = M^-4`,

the exposed one-generation residual powers are bounded by a constant times
`M^-2`, while the linear signal is `M^-1`.  The analytic PDE estimates that
produce those residual terms are NOT formalized here.
-/

namespace Millennium.NavierStokes.OneGenMasterDiagonal

/-- The four `M^-2` terms, the returned-base `2 M^-3` term, and the
packet-viscosity `M^-5` term are dominated by `7 M^-2` once `M >= 1`,
expressed after multiplication by `M^5` to avoid any order-sensitive division. -/
theorem residual_polynomial_bound (M : ℚ) (hM : 1 ≤ M) :
    4 * M^3 + 2 * M^2 + 1 ≤ 7 * M^3 := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have h2 : M^2 ≤ M^3 := by
    calc
      M^2 = 1 * M^2 := by ring
      _ ≤ M * M^2 := mul_le_mul_of_nonneg_right hM (sq_nonneg M)
      _ = M^3 := by ring
  have hM_sq : M ≤ M^2 := by
    calc
      M = M * 1 := by ring
      _ ≤ M * M := mul_le_mul_of_nonneg_left hM hM0
      _ = M^2 := by ring
  have h1 : 1 ≤ M^3 := le_trans hM (le_trans hM_sq h2)
  nlinarith

/-- On the same diagonal, the residual-to-signal exponent numerator is
`4 M^3 + 2 M^2 + 1`, and it is at most `7 M^3`.
This is the exact finite algebra behind an `O(M^-1)` relative error. -/
theorem relative_numerator_bound (M : ℚ) (hM : 1 ≤ M) :
    4 * M^3 + 2 * M^2 + 1 ≤ 7 * M^3 :=
  residual_polynomial_bound M hM

/-- If the master scale is large enough to absorb a finite constant `C`
against a requested fraction `eta`, then the `7 C / M` envelope is below
`eta`. -/
theorem absorb_finite_constant
    (M C eta : ℚ) (hM : 0 < M) (hbudget : 7 * C ≤ eta * M) :
    7 * C / M ≤ eta := by
  exact (div_le_iff₀ hM).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hbudget)

/-- A convenient combined finite-core certificate: polynomial dominance plus
absorption of the fixed analytic constant. -/
theorem master_diagonal_certificate
    (M C eta : ℚ) (hM1 : 1 ≤ M) (hbudget : 7 * C ≤ eta * M) :
    (4 * M^3 + 2 * M^2 + 1 ≤ 7 * M^3) ∧
    (7 * C / M ≤ eta) := by
  constructor
  · exact residual_polynomial_bound M hM1
  · have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM1
    exact absorb_finite_constant M C eta hM0 hbudget

#print axioms residual_polynomial_bound
#print axioms relative_numerator_bound
#print axioms absorb_finite_constant
#print axioms master_diagonal_certificate

end Millennium.NavierStokes.OneGenMasterDiagonal
