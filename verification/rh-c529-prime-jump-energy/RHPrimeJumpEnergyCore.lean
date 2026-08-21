import Mathlib

/-!
# RH C529 finite prime-jump energy core

Finite real algebra only.  This file formalizes the positive-part energy used
in the C529 ordinary-prime jump balance and a two-step shadow of the monotone
selector/prefix-max dual.

It does not formalize primes, Chebyshev functions, Stieltjes integration,
Suzuki/Landau, zeta zeros, BGST, or RH.
-/

namespace Millennium
namespace RH
namespace C529

/-- One-sided positive part. -/
def pos (x : ℝ) : ℝ := max x 0

/-- Convex one-sided quadratic energy `1/2 [x]_+^2`. -/
noncomputable def energy (x : ℝ) : ℝ := (pos x) ^ 2 / 2

/-- Energy injected by a positive jump of size `a`. -/
noncomputable def jumpEnergy (r a : ℝ) : ℝ := energy (r + a) - energy r

/-- Algebraic energy lost during a downward drift of length `g`. -/
noncomputable def driftEnergy (r g : ℝ) : ℝ := energy r - energy (r - g)

theorem pos_nonneg (x : ℝ) : 0 ≤ pos x := by
  exact le_max_right x 0

theorem pos_mono {x y : ℝ} (hxy : x ≤ y) : pos x ≤ pos y := by
  unfold pos
  exact max_le_max hxy le_rfl

theorem energy_nonneg (x : ℝ) : 0 ≤ energy x := by
  unfold energy
  positivity

theorem energy_mono {x y : ℝ} (hxy : x ≤ y) : energy x ≤ energy y := by
  have hx : 0 ≤ pos x := pos_nonneg x
  have hy : 0 ≤ pos y := pos_nonneg y
  have hp : pos x ≤ pos y := pos_mono hxy
  unfold energy
  nlinarith

/-- A nonnegative jump can only add one-sided energy. -/
theorem jumpEnergy_nonneg {r a : ℝ} (ha : 0 ≤ a) :
    0 ≤ jumpEnergy r a := by
  unfold jumpEnergy
  exact sub_nonneg.mpr (energy_mono (by linarith))

/-- Positive-state jump formula. -/
theorem jumpEnergy_of_nonneg
    {r a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) :
    jumpEnergy r a = a * r + a ^ 2 / 2 := by
  have hra : 0 ≤ r + a := by linarith
  simp [jumpEnergy, energy, pos, max_eq_left hr, max_eq_left hra]
  ring

/-- Crossing-from-negative jump formula. -/
theorem jumpEnergy_of_crossing
    {r a : ℝ} (hr : r ≤ 0) (hra : 0 ≤ r + a) :
    jumpEnergy r a = (r + a) ^ 2 / 2 := by
  simp [jumpEnergy, energy, pos, max_eq_right hr, max_eq_left hra]

/-- A jump remaining below zero injects no positive energy. -/
theorem jumpEnergy_of_below
    {r a : ℝ} (hr : r ≤ 0) (hra : r + a ≤ 0) :
    jumpEnergy r a = 0 := by
  simp [jumpEnergy, energy, pos, max_eq_right hr, max_eq_right hra]

/-- Splitting one arrival into two positive sub-arrivals is exactly telescopic. -/
theorem jumpEnergy_add_split (r a b : ℝ) :
    jumpEnergy r (a + b) = jumpEnergy r a + jumpEnergy (r + a) b := by
  unfold jumpEnergy
  ring

/-- A nonnegative downward drift can only remove one-sided energy. -/
theorem driftEnergy_nonneg {r g : ℝ} (hg : 0 ≤ g) :
    0 ≤ driftEnergy r g := by
  unfold driftEnergy
  exact sub_nonneg.mpr (energy_mono (by linarith))

/-- Exact one-jump/one-drift energy ledger. -/
theorem jump_drift_balance (r a g : ℝ) :
    driftEnergy (r + a) g =
      energy r + jumpEnergy r a - energy (r + a - g) := by
  unfold driftEnergy jumpEnergy
  ring

/-- Two-step finite shadow of the monotone-selector/prefix-max dual.
For `1 ≥ v₁ ≥ v₂ ≥ 0`, the weighted increment is bounded by the
largest of the zero, first-prefix, and second-prefix sums. -/
theorem twoStep_monotone_selector_le_prefixMax
    (d1 d2 v1 v2 : ℝ)
    (hv1 : v1 ≤ 1) (hv12 : v2 ≤ v1) (hv2 : 0 ≤ v2) :
    v1 * d1 + v2 * d2 ≤ max 0 (max d1 (d1 + d2)) := by
  let M : ℝ := max 0 (max d1 (d1 + d2))
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact le_max_left _ _
  have hd1M : d1 ≤ M := by
    dsimp [M]
    exact (le_max_left d1 (d1 + d2)).trans (le_max_right 0 (max d1 (d1 + d2)))
  have hsumM : d1 + d2 ≤ M := by
    dsimp [M]
    exact (le_max_right d1 (d1 + d2)).trans (le_max_right 0 (max d1 (d1 + d2)))
  have hw1 : 0 ≤ v1 - v2 := sub_nonneg.mpr hv12
  have h1 : (v1 - v2) * d1 ≤ (v1 - v2) * M :=
    mul_le_mul_of_nonneg_left hd1M hw1
  have h2 : v2 * (d1 + d2) ≤ v2 * M :=
    mul_le_mul_of_nonneg_left hsumM hv2
  have hv10 : 0 ≤ v1 := hv2.trans hv12
  have hvM : v1 * M ≤ M := by
    nlinarith
  change v1 * d1 + v2 * d2 ≤ M
  nlinarith

#print axioms pos_nonneg
#print axioms pos_mono
#print axioms energy_nonneg
#print axioms energy_mono
#print axioms jumpEnergy_nonneg
#print axioms jumpEnergy_of_nonneg
#print axioms jumpEnergy_of_crossing
#print axioms jumpEnergy_of_below
#print axioms jumpEnergy_add_split
#print axioms driftEnergy_nonneg
#print axioms jump_drift_balance
#print axioms twoStep_monotone_selector_le_prefixMax

end C529
end RH
end Millennium
