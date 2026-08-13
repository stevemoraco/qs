import Mathlib

/-!
# Critical Chebyshev frozen-prefix finite firewall

This file formalizes only the algebraic/order-theoretic layer behind the
frozen-prime-prefix lower envelope found in the weighted Chebyshev RH lane.

For positive `x` and nonnegative `Theta`, the elementary function

`sqrt x + Theta / sqrt x`

has exact defect from its minimum `2 * sqrt Theta`

`(sqrt x - sqrt Theta)^2 / sqrt x`.

The file also records the polynomial reserve factorization and its exact
one-step increment. It does **not** define primes, the Chebyshev function,
the Riemann zeta function, or RH, and it imports no analytic equivalence.
-/

namespace Millennium.RH.CriticalChebyshevFrozenPrefix

def reserve (theta a arch : ℝ) : ℝ :=
  2 * Real.sqrt theta - arch - a

def polynomialReserve (theta a arch : ℝ) : ℝ :=
  4 * theta - (a + arch) ^ 2

theorem sqrt_add_div_sub_min
    {x theta : ℝ} (hx : 0 < x) (htheta : 0 ≤ theta) :
    Real.sqrt x + theta / Real.sqrt x - 2 * Real.sqrt theta =
      (Real.sqrt x - Real.sqrt theta) ^ 2 / Real.sqrt x := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsx_ne : Real.sqrt x ≠ 0 := ne_of_gt hsx
  have hsx_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  have hst_sq : (Real.sqrt theta) ^ 2 = theta := Real.sq_sqrt htheta
  field_simp [hsx_ne]
  nlinarith

theorem reserve_le_frozen
    {x theta a arch : ℝ} (hx : 0 < x) (htheta : 0 ≤ theta) :
    reserve theta a arch ≤
      Real.sqrt x + theta / Real.sqrt x - arch - a := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsq : 0 ≤ (Real.sqrt x - Real.sqrt theta) ^ 2 / Real.sqrt x :=
    div_nonneg (sq_nonneg _) hsx.le
  have hid := sqrt_add_div_sub_min hx htheta
  dsimp [reserve]
  linarith

theorem frozen_at_minimizer
    {theta a arch : ℝ} (htheta : 0 < theta) :
    Real.sqrt theta + theta / Real.sqrt theta - arch - a =
      reserve theta a arch := by
  have hs : Real.sqrt theta ≠ 0 := ne_of_gt (Real.sqrt_pos.2 htheta)
  have hs_sq : (Real.sqrt theta) ^ 2 = theta := Real.sq_sqrt htheta.le
  dsimp [reserve]
  field_simp [hs]
  nlinarith

theorem weighted_tail_nonpos
    {ι : Type*} (s : Finset ι) (weight defect : ι → ℝ)
    (hweight : ∀ i ∈ s, 0 ≤ weight i)
    (hdefect : ∀ i ∈ s, defect i ≤ 0) :
    ∑ i ∈ s, weight i * defect i ≤ 0 := by
  exact Finset.sum_nonpos fun i hi =>
    mul_nonpos_of_nonneg_of_nonpos (hweight i hi) (hdefect i hi)

theorem polynomial_reserve_factorization
    {theta a arch : ℝ} (htheta : 0 ≤ theta) :
    polynomialReserve theta a arch =
      (2 * Real.sqrt theta + a + arch) * reserve theta a arch := by
  have hs_sq : (Real.sqrt theta) ^ 2 = theta := Real.sq_sqrt htheta
  dsimp [polynomialReserve, reserve]
  nlinarith

theorem polynomial_reserve_pos_iff
    {theta a arch : ℝ} (htheta : 0 < theta) (ha : 0 ≤ a + arch) :
    0 < polynomialReserve theta a arch ↔ 0 < reserve theta a arch := by
  have hfactor : 0 < 2 * Real.sqrt theta + a + arch := by
    have hs : 0 < Real.sqrt theta := Real.sqrt_pos.2 htheta
    linarith
  rw [polynomial_reserve_factorization htheta.le]
  constructor
  · intro hprod
    by_contra hnot
    have hres : reserve theta a arch ≤ 0 := le_of_not_gt hnot
    have hnonpos :
        (2 * Real.sqrt theta + a + arch) * reserve theta a arch ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hfactor.le hres
    linarith
  · intro hres
    exact mul_pos hfactor hres

theorem polynomial_reserve_increment
    (theta a arch ell root : ℝ) (hroot : root ≠ 0) :
    polynomialReserve (theta + ell) (a + ell / root) arch -
        polynomialReserve theta a arch =
      ell * (4 - 2 * (a + arch) / root - ell / (root * root)) := by
  dsimp [polynomialReserve]
  field_simp [hroot]
  ring

theorem clamped_reserve_eq_scalar_add_square
    {x theta a arch : ℝ} (hx : 0 < x) (htheta : 0 ≤ theta) :
    Real.sqrt x + theta / Real.sqrt x - arch - a =
      reserve theta a arch +
        (Real.sqrt x - Real.sqrt theta) ^ 2 / Real.sqrt x := by
  have hid := sqrt_add_div_sub_min hx htheta
  dsimp [reserve]
  linarith

#print axioms sqrt_add_div_sub_min
#print axioms reserve_le_frozen
#print axioms frozen_at_minimizer
#print axioms weighted_tail_nonpos
#print axioms polynomial_reserve_factorization
#print axioms polynomial_reserve_pos_iff
#print axioms polynomial_reserve_increment
#print axioms clamped_reserve_eq_scalar_add_square

end Millennium.RH.CriticalChebyshevFrozenPrefix
