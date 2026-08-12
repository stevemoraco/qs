import Mathlib

/-!
# Round 209 Navier--Stokes dissipation-restart finite cores

This file formalizes only scalar averaging, lifespan-budget and exponent
identities. It does not formalize Navier--Stokes local theory, energy equality,
partial regularity, singularities, or the Clay problem.
-/

namespace Millennium
namespace Round209NavierStokes

/-- A good-time average bound and a square-root terminal dissipation budget
supply the scalar lifespan inequality needed to cross the remaining interval. -/
theorem terminal_tail_budget_implies_restart_budget
    (s D X c : ℝ)
    (hs : 0 < s)
    (hD : 0 ≤ D)
    (hX : 0 ≤ X)
    (hc : 0 ≤ c)
    (haverage : s * X ≤ 2 * D)
    (htail : 4 * D ^ 2 ≤ c * s) :
    s * X ^ 2 ≤ c := by
  have hdiff : 0 ≤ 2 * D - s * X := by linarith
  have hsum : 0 ≤ 2 * D + s * X := by positivity
  have hprod : 0 ≤ (2 * D - s * X) * (2 * D + s * X) :=
    mul_nonneg hdiff hsum
  have hsq : s ^ 2 * X ^ 2 ≤ 4 * D ^ 2 := by
    nlinarith
  have hsc : s ^ 2 * X ^ 2 ≤ c * s := hsq.trans htail
  have hmul : s * (s * X ^ 2) ≤ s * c := by
    nlinarith
  exact (mul_le_mul_iff_of_pos_left hs).mp hmul

/-- Dyadic terminal shell length for the scalar countermodel. -/
def shellLength (n : ℕ) : ℚ := (1 / 16 : ℚ) ^ n

/-- Dyadic enstrophy height for the scalar countermodel. -/
def shellEnstrophy (n : ℕ) : ℚ := (8 : ℚ) ^ n

/-- Every shell contributes the summable amount `2^{-n}` to total dissipation. -/
theorem shell_dissipation_identity (n : ℕ) :
    shellLength n * shellEnstrophy n = (1 / 2 : ℚ) ^ n := by
  rw [shellLength, shellEnstrophy, ← mul_pow]
  norm_num

/-- The same shell has restart product `4^n`, which grows rather than shrinks. -/
theorem shell_restart_product_identity (n : ℕ) :
    shellLength n * shellEnstrophy n ^ 2 = (4 : ℚ) ^ n := by
  rw [shellLength, shellEnstrophy, pow_two, ← mul_pow, ← mul_pow]
  norm_num

/-- The energy-interpolation Sobolev restart exponent is strictly superlinear
for every subcritical index `s>1/2`. -/
theorem sobolev_restart_exponent_superlinear
    (s : ℝ) (hs : 1 / 2 < s) :
    1 < s / (s - 1 / 2) := by
  have hden : 0 < s - 1 / 2 := by linarith
  rw [lt_div_iff₀ hden]
  linarith

/-- The corresponding exponent on the energy-line `L^p_t L^q_x` currency is
strictly superlinear for every `q>3`. -/
theorem lebesgue_restart_exponent_superlinear
    (q : ℝ) (hq : 3 < q) :
    1 < 3 * (q - 2) / (2 * (q - 3)) := by
  have hden : 0 < 2 * (q - 3) := by linarith
  rw [lt_div_iff₀ hden]
  linarith

/-- The square-root terminal-tail criterion is exactly the scalar condition
`4D^2 <= c s` used by the restart budget. -/
theorem square_root_tail_suffices
    (D c s : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hroot : 2 * D ≤ Real.sqrt c * Real.sqrt s) :
    4 * D ^ 2 ≤ c * s := by
  have hsq : (2 * D) ^ 2 ≤ (Real.sqrt c * Real.sqrt s) ^ 2 := by
    exact sq_le_sq₀ (by positivity) hroot
  calc
    4 * D ^ 2 = (2 * D) ^ 2 := by ring
    _ ≤ (Real.sqrt c * Real.sqrt s) ^ 2 := hsq
    _ = c * s := by
      rw [mul_pow, Real.sq_sqrt hc, Real.sq_sqrt hs]

#print axioms terminal_tail_budget_implies_restart_budget
#print axioms shell_dissipation_identity
#print axioms shell_restart_product_identity
#print axioms sobolev_restart_exponent_superlinear
#print axioms lebesgue_restart_exponent_superlinear
#print axioms square_root_tail_suffices

end Round209NavierStokes
end Millennium
