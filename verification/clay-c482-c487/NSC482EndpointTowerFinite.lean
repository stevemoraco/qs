import Mathlib

namespace NS
namespace C482EndpointTowerFinite

open Finset
open scoped BigOperators

def enstrophyPartial (n : ℕ) : ℚ :=
  ∑ j in range n, (1 / 4 : ℚ) ^ j

def palinstrophyPartial (n : ℕ) : ℚ :=
  ∑ j in range n, (1 / 64 : ℚ) ^ j

theorem enstrophyPartial_succ (n : ℕ) :
    enstrophyPartial (n + 1) =
      enstrophyPartial n + (1 / 4 : ℚ) ^ n := by
  simp [enstrophyPartial, sum_range_succ]

theorem palinstrophyPartial_succ (n : ℕ) :
    palinstrophyPartial (n + 1) =
      palinstrophyPartial n + (1 / 64 : ℚ) ^ n := by
  simp [palinstrophyPartial, sum_range_succ]

theorem enstrophyPartial_closed (n : ℕ) :
    enstrophyPartial n =
      (4 / 3 : ℚ) * (1 - (1 / 4 : ℚ) ^ n) := by
  induction n with
  | zero => simp [enstrophyPartial]
  | succ n ih =>
      rw [enstrophyPartial_succ, ih, pow_succ]
      ring

theorem palinstrophyPartial_closed (n : ℕ) :
    palinstrophyPartial n =
      (64 / 63 : ℚ) * (1 - (1 / 64 : ℚ) ^ n) := by
  induction n with
  | zero => simp [palinstrophyPartial]
  | succ n ih =>
      rw [palinstrophyPartial_succ, ih, pow_succ]
      ring

theorem enstrophyPartial_lt (n : ℕ) :
    enstrophyPartial n < (4 / 3 : ℚ) := by
  rw [enstrophyPartial_closed]
  have hp : 0 < (1 / 4 : ℚ) ^ n := by positivity
  nlinarith

theorem palinstrophyPartial_lt (n : ℕ) :
    palinstrophyPartial n < (64 / 63 : ℚ) := by
  rw [palinstrophyPartial_closed]
  have hp : 0 < (1 / 64 : ℚ) ^ n := by positivity
  nlinarith

theorem constant_cubic_mass (n : ℕ) :
    (∑ _j in range n, (1 : ℕ)) = n := by
  simp

theorem projected_midband_floor
    {m active low mid high : ℝ}
    (_hm : 0 ≤ m)
    (hactive : m / 4 ≤ active)
    (hlow : low ≤ m / 16)
    (hhigh : high ≤ m / 16)
    (hdecomp : active = low + mid + high) :
    m / 8 ≤ mid := by
  linarith

theorem triad_coefficients_sum_zero :
    (2 : ℚ) + (-1) + (-1) = 0 := by norm_num

theorem triad_nonzero_equilibrium :
    ((-2 : ℚ) * (-1) = 2 * 1 * 1) ∧
    ((1 : ℚ) * 1 = (-1) * 1 * (-1)) ∧
    ((1 : ℚ) * 1 = (-1) * (-1) * 1) := by norm_num

theorem triad_linear_energy_balance :
    ((-2 : ℚ) * (-1) ^ 2 +
      (1 : ℚ) * 1 ^ 2 +
      (1 : ℚ) * 1 ^ 2) = 0 := by norm_num

theorem triad_nondegenerate :
    ((-1 : ℚ) ≠ 0) ∧ ((1 : ℚ) ≠ 0) ∧
    ((2 : ℚ) ≠ 0) ∧ ((-1 : ℚ) ≠ 0) := by norm_num

#print axioms enstrophyPartial_closed
#print axioms palinstrophyPartial_closed
#print axioms projected_midband_floor
#print axioms triad_nonzero_equilibrium

end C482EndpointTowerFinite
end NS
