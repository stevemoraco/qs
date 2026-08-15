import Mathlib

/-!
# RH B160B deep-run two-slack finite core

Finite exponent and finite-sum algebra only.

The human B160B reduction permits both a growing negative-depth threshold and a
growing allowed run length.  An off-critical zero beats the threshold through
its power-scale depth and beats the run allowance through its power-scale
persistence.  These declarations formalize only the scalar exponent and finite
window-sum consequences.

They do not formalize Bhattacharya--Martin--Simpson, Landau, reciprocal-prime
Mertens estimates, primes, zeta zeros, BGST, B46, or RH.
-/

namespace RHDeepRunTwoSlackFinite

open Finset
open scoped BigOperators

/-- Exceeding the depth half-bound means the off-critical depth exponent exceeds
the prescribed threshold exponent. -/
theorem beyond_depth_threshold
    {beta theta : ℝ} (h : theta / 2 < beta) :
    theta < 2 * beta := by
  linarith

/-- Exceeding the run half-bound leaves sampled-run exponent larger than the
allowed exponent. -/
theorem beyond_run_threshold
    {beta sigma eta : ℝ}
    (h : (1 + sigma + eta) / 2 < beta) :
    eta < 2 * beta - 1 - sigma := by
  linarith

/-- The critical-line depth exponent in square-root coordinates is exactly one. -/
theorem critical_depth_exponent :
    2 * (1 / 2 : ℝ) = 1 := by
  norm_num

/-- At exact run-boundary exponent, paying sampler gap leaves precisely the
allowed sampled-run exponent. -/
theorem hostile_run_boundary_exact (sigma eta : ℝ) :
    (sigma + eta) - sigma = eta := by
  ring

/-- At exact depth boundary, doubling the half-bound recovers the threshold
exponent. -/
theorem hostile_depth_boundary_exact (theta : ℝ) :
    2 * (theta / 2) = theta := by
  ring

/-- If every value in a finite window is at most `-D`, the entire signed window
sum is at most minus cardinality times `D`. -/
theorem all_deep_negative_sum_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (D : ℝ)
    (hdeep : ∀ i ∈ s, x i ≤ -D) :
    (∑ i ∈ s, x i) ≤ -((s.card : ℝ) * D) := by
  calc
    (∑ i ∈ s, x i) ≤ ∑ _i ∈ s, (-D) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hdeep i hi
    _ = -((s.card : ℝ) * D) := by
      simp
      ring

/-- A nonempty window uniformly below `-D` violates every average floor with a
strictly smaller depth threshold `T`. -/
theorem deep_window_breaks_shallower_floor
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (D T : ℝ)
    (hs : 0 < s.card)
    (hTD : T < D)
    (hdeep : ∀ i ∈ s, x i ≤ -D) :
    (∑ i ∈ s, x i) < -((s.card : ℝ) * T) := by
  have hsum := all_deep_negative_sum_le s x D hdeep
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hstrict : -((s.card : ℝ) * D) < -((s.card : ℝ) * T) := by
    nlinarith
  exact lt_of_le_of_lt hsum hstrict

#print axioms beyond_depth_threshold
#print axioms beyond_run_threshold
#print axioms critical_depth_exponent
#print axioms hostile_run_boundary_exact
#print axioms hostile_depth_boundary_exact
#print axioms all_deep_negative_sum_le
#print axioms deep_window_breaks_shallower_floor

end RHDeepRunTwoSlackFinite
