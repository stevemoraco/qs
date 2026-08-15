import Mathlib

open scoped BigOperators

/-!
# RH B152 finite prime-gap hinge / box core

Finite real algebra only.

For a cell of nonnegative length `ell`, whose one-sided state starts at `a` and
then drifts with slope `-1`, the negative area is the exact box-constrained
concave quadratic maximum

`sup_{0 <= theta <= ell} theta * (ell - a) - theta^2 / 2`.

The declarations below formalize only that finite optimization algebra and the
hostile unboxed overcharge.  They do not formalize primes, Mertens sums, Mellin
transforms, Landau's theorem, zeta zeros, BGST matrices, or RH.
-/

namespace RHB152PrimeGapHingeFinite

/-- Exact one-cell negative-area ledger in its three elementary regimes. -/
def hingeArea (a ell : Real) : Real :=
  if a <= 0 then (-a) * ell + ell ^ 2 / 2
  else if a < ell then (ell - a) ^ 2 / 2
  else 0

/-- Concave quadratic objective whose box maximum is the one-cell area. -/
def hingeObjective (a ell theta : Real) : Real :=
  theta * (ell - a) - theta ^ 2 / 2

/-- Explicit clipping optimizer. -/
def hingeOptimizer (a ell : Real) : Real :=
  if a <= 0 then ell
  else if a < ell then ell - a
  else 0

/-- Every feasible box point lies below the exact hinge area. -/
theorem hingeObjective_le_hingeArea
    {a ell theta : Real}
    (hell : 0 <= ell)
    (htheta0 : 0 <= theta)
    (hthetaell : theta <= ell) :
    hingeObjective a ell theta <= hingeArea a ell := by
  by_cases ha0 : a <= 0
  · have h1 : 0 <= ell - theta := sub_nonneg.mpr hthetaell
    have h2 : 0 <= ell - theta - 2 * a := by
      linarith
    have hmul : 0 <= (ell - theta) * (ell - theta - 2 * a) :=
      mul_nonneg h1 h2
    simp [hingeArea, hingeObjective, ha0]
    nlinarith
  · have ha : 0 < a := lt_of_not_ge ha0
    by_cases haell : a < ell
    · have hsq : 0 <= (theta - (ell - a)) ^ 2 := sq_nonneg _
      simp [hingeArea, hingeObjective, ha0, haell]
      nlinarith
    · have hle : ell <= a := le_of_not_gt haell
      have hprod : theta * (ell - a) <= 0 :=
        mul_nonpos_of_nonneg_of_nonpos htheta0 (sub_nonpos.mpr hle)
      have hsq : 0 <= theta ^ 2 := sq_nonneg theta
      simp [hingeArea, hingeObjective, ha0, haell]
      linarith

/-- The explicit optimizer always belongs to the box. -/
theorem hingeOptimizer_feasible
    {a ell : Real} (hell : 0 <= ell) :
    0 <= hingeOptimizer a ell ∧ hingeOptimizer a ell <= ell := by
  by_cases ha0 : a <= 0
  · simp [hingeOptimizer, ha0, hell]
  · have ha : 0 < a := lt_of_not_ge ha0
    by_cases haell : a < ell
    · have hpos : 0 <= ell - a := le_of_lt (sub_pos.mpr haell)
      have hle : ell - a <= ell := by linarith
      simp [hingeOptimizer, ha0, haell, hpos, hle]
    · simp [hingeOptimizer, ha0, haell, hell]

/-- The clipping optimizer attains the exact hinge area. -/
theorem hingeOptimizer_attains
    {a ell : Real} (hell : 0 <= ell) :
    hingeObjective a ell (hingeOptimizer a ell) = hingeArea a ell := by
  by_cases ha0 : a <= 0
  · simp [hingeOptimizer, hingeArea, hingeObjective, ha0]
    ring
  · have ha : 0 < a := lt_of_not_ge ha0
    by_cases haell : a < ell
    · simp [hingeOptimizer, hingeArea, hingeObjective, ha0, haell]
      ring
    · simp [hingeOptimizer, hingeArea, hingeObjective, ha0, haell]

/-- Finite box objective is bounded termwise by the finite hinge-area sum. -/
theorem finite_hinge_sum_upper
    {I : Type*} (s : Finset I)
    (a ell theta : I -> Real)
    (hell : forall i in s, 0 <= ell i)
    (htheta0 : forall i in s, 0 <= theta i)
    (hthetaell : forall i in s, theta i <= ell i) :
    (∑ i in s, hingeObjective (a i) (ell i) (theta i)) <=
      ∑ i in s, hingeArea (a i) (ell i) := by
  apply Finset.sum_le_sum
  intro i hi
  exact hingeObjective_le_hingeArea
    (hell i hi) (htheta0 i hi) (hthetaell i hi)

/-- The coordinatewise clipping optimizer attains the finite hinge-area sum. -/
theorem finite_hinge_optimizer_attains
    {I : Type*} (s : Finset I)
    (a ell : I -> Real)
    (hell : forall i in s, 0 <= ell i) :
    (∑ i in s,
      hingeObjective (a i) (ell i) (hingeOptimizer (a i) (ell i))) =
      ∑ i in s, hingeArea (a i) (ell i) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact hingeOptimizer_attains (hell i hi)

/-- Hostile firewall: removing the upper box can overcharge a fully negative
cell by exactly `M^2 / 2`. -/
theorem unboxed_negative_cell_overcharge (M ell : Real) :
    ((ell + M) ^ 2 / 2) - (M * ell + ell ^ 2 / 2) = M ^ 2 / 2 := by
  ring

#print axioms hingeObjective_le_hingeArea
#print axioms hingeOptimizer_feasible
#print axioms hingeOptimizer_attains
#print axioms finite_hinge_sum_upper
#print axioms finite_hinge_optimizer_attains
#print axioms unboxed_negative_cell_overcharge

end RHB152PrimeGapHingeFinite
