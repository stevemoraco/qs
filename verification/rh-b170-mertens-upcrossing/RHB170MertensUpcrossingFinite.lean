import Mathlib

/-!
# RH B170 reciprocal-Mertens upcrossing finite core

Finite real/Finset algebra only.

The human B170 reduction selects prime events where the reciprocal-prime Mertens
state crosses upward through zero.  If `a = p * R_-(p)`, the upcrossing condition
is exactly `-1 <= a <= 0`; after the prime jump the scaled state is `1+a`, hence
lies in `[0,1]`.  The prime-harmonic state has the finite scalar form

`F(p) = (1+a) - race`,

where `race = pi(p)-li(p)`.

The declarations below formalize only the load-bearing consequences of that
scalar ledger and the finite zero-bad-count endpoint.  They do NOT formalize
primes, `li`, reciprocal-prime Mertens theory, Bhattacharya--Martin--Simpson,
Landau's theorem, zeta, BGST/Hermite matrices, B46, or RH.
-/

namespace RHB170MertensUpcrossingFinite

/-- At an upcrossing prime, the post-jump scaled reciprocal-Mertens state lies
in the unit interval.  Here `a` shadows `p * R_-(p)`. -/
theorem upcross_postweight_bounds
    {a : ℝ} (hlo : -1 ≤ a) (hhi : a ≤ 0) :
    0 ≤ 1 + a ∧ 1 + a ≤ 1 := by
  constructor <;> linarith

/-- If the prime-harmonic state is nonnegative at an upcrossing, then the raw
prime-counting excess is at most one. -/
theorem nonnegative_upcrossing_forces_race_le_one
    {a race f : ℝ}
    (hlo : -1 ≤ a) (hhi : a ≤ 0)
    (hf : f = (1 + a) - race)
    (hfnonneg : 0 ≤ f) :
    race ≤ 1 := by
  have hpost := (upcross_postweight_bounds hlo hhi).2
  linarith

/-- A depth-`D` negative local minimum at an upcrossing forces prime-counting
excess at least `D`. -/
theorem deep_upcrossing_forces_large_race
    {a race f D : ℝ}
    (hlo : -1 ≤ a) (hhi : a ≤ 0)
    (hD : 0 ≤ D)
    (hf : f = (1 + a) - race)
    (hdeep : f ≤ -D) :
    D ≤ race := by
  have hpost := (upcross_postweight_bounds hlo hhi).1
  linarith

/-- More generally, the exact race excess above a finite threshold is paid by
negative depth once the post-jump upcrossing weight is nonnegative. -/
theorem threshold_violation_forces_negative_state
    {a race C f : ℝ}
    (hlo : -1 ≤ a) (hhi : a ≤ 0)
    (hC : 0 ≤ C)
    (hf : f = (1 + a) - race)
    (hrace : 1 + C < race) :
    f < -C := by
  have hpost := (upcross_postweight_bounds hlo hhi).2
  linarith

/-- Finite shadow of zero-threshold diagonal inertia: zero bad count is exactly
coordinatewise boundedness by the chosen race ceiling. -/
def badCount {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (race : ι → ℝ) (C : ℝ) : ℕ :=
  (s.filter fun i => C < race i).card

theorem badCount_eq_zero_iff
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (race : ι → ℝ) (C : ℝ) :
    badCount s race C = 0 ↔ ∀ i ∈ s, race i ≤ C := by
  simp [badCount, not_lt]

/-- Coordinatewise boundedness makes every nonnegative finite selector of the
centered race nonpositive.  This is the finite signed-dispersion direction. -/
theorem selector_sum_nonpos_of_race_bound
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (race phi : ι → ℝ) (C : ℝ)
    (hphi : ∀ i ∈ s, 0 ≤ phi i)
    (hbound : ∀ i ∈ s, race i ≤ C) :
    ∑ i ∈ s, phi i * (race i - C) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  exact mul_nonpos_of_nonneg_of_nonpos (hphi i hi) (sub_nonpos.mpr (hbound i hi))

#check upcross_postweight_bounds
#check nonnegative_upcrossing_forces_race_le_one
#check deep_upcrossing_forces_large_race
#check threshold_violation_forces_negative_state
#check badCount_eq_zero_iff
#check selector_sum_nonpos_of_race_bound

#print axioms upcross_postweight_bounds
#print axioms nonnegative_upcrossing_forces_race_le_one
#print axioms deep_upcrossing_forces_large_race
#print axioms threshold_violation_forces_negative_state
#print axioms badCount_eq_zero_iff
#print axioms selector_sum_nonpos_of_race_bound

end RHB170MertensUpcrossingFinite
