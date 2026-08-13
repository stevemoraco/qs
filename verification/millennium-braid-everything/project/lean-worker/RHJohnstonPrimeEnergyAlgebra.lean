import Mathlib

namespace RHJohnstonPrimeEnergyAlgebra

/-- Algebraic cancellation behind the Johnston prime-staircase energy.
If `D = x^2/2 - 2 - x*theta + weighted` and `s=x-theta`, then
`D-s^2/2 = weighted-theta^2/2-2`.  No number theory is assumed here. -/
theorem prime_staircase_energy_identity
    {x theta weighted D s : ℝ}
    (hD : D = x^2 / 2 - 2 - x * theta + weighted)
    (hs : s = x - theta) :
    D - s^2 / 2 = weighted - theta^2 / 2 - 2 := by
  rw [hD, hs]
  ring

/-- Exact one-prime energy jump.  Here `thetaPrev` is the log-primorial
before adjoining a prime with logarithm `ell`, and `p` is that prime. -/
theorem one_prime_energy_jump
    {p ell thetaPrev : ℝ} :
    p * ell - ((thetaPrev + ell)^2 - thetaPrev^2) / 2
      = ell * (p - thetaPrev) - ell^2 / 2 := by
  ring

/-- Between prime jumps the flow `D'=s`, `s'=1` preserves the quadratic
combination `D-s^2/2`; this finite difference version is the algebraic core. -/
theorem gap_energy_preserved
    {D0 s0 u D1 s1 : ℝ}
    (hD : D1 = D0 + s0 * u + u^2 / 2)
    (hs : s1 = s0 + u) :
    D1 - s1^2 / 2 = D0 - s0^2 / 2 := by
  rw [hD, hs]
  ring

/-- Exact removal of Johnston's c=3/2 weighted integral once the staircase
integration has produced the displayed scalar identity. -/
theorem three_halves_sign_reduction
    {J A theta rootx root2 : ℝ}
    (hJ : J = 2 * (A - theta / rootx - rootx + root2)) :
    J < 0 ↔ A < rootx + theta / rootx - root2 := by
  rw [hJ]
  constructor <;> intro h <;> linarith

/-- Multiplying the two-sum inequality by a positive square root gives the
single positive-kernel prime-sum coordinate. -/
theorem two_sum_to_single_kernel
    {A theta r c : ℝ}
    (hr : 0 < r) :
    A < r + theta / r - c ↔ r * A - theta < r^2 - c * r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hid : r * (r + theta / r - c) = r^2 + theta - c * r := by
    field_simp [hr0]
    ring
  constructor
  · intro h
    have hm : r * A < r * (r + theta / r - c) :=
      (mul_lt_mul_left hr).2 h
    rw [hid] at hm
    linarith
  · intro h
    have hm : r * A < r^2 + theta - c * r := by
      linarith
    rw [← hid] at hm
    exact (mul_lt_mul_left hr).1 hm

#print axioms prime_staircase_energy_identity
#print axioms one_prime_energy_jump
#print axioms gap_energy_preserved
#print axioms three_halves_sign_reduction
#print axioms two_sum_to_single_kernel

end RHJohnstonPrimeEnergyAlgebra
