import Mathlib

/-!
# Seventh-object and inversion exactness firewall

This module verifies three things:

* finite scale propagation is ordinary induction;
* the current route wrapper has exactly the logical strength of its goal;
* the inversion density has one determinant weight, not two.
-/

namespace MillenniumGrandExactObject

structure SeventhObject where
  good : ℕ → Prop
  seed : good 0
  propagate : ∀ n : ℕ, good n → good (n + 1)

theorem SeventhObject.allScales (C : SeventhObject) :
    ∀ n : ℕ, C.good n := by
  intro n
  induction n with
  | zero => exact C.seed
  | succ n ih => exact C.propagate n ih

structure PrizeRoute (Goal : Prop) where
  certificate : SeventhObject
  frontier : Prop
  allScalesToFrontier : (∀ n : ℕ, certificate.good n) → frontier
  frontierToGoal : frontier → Goal

theorem PrizeRoute.solve {Goal : Prop} (R : PrizeRoute Goal) : Goal := by
  exact R.frontierToGoal
    (R.allScalesToFrontier R.certificate.allScales)

private def trivialCertificate : SeventhObject where
  good := fun _ => True
  seed := True.intro
  propagate := fun _ _ => True.intro

theorem nonempty_prizeRoute_iff (Goal : Prop) :
    Nonempty (PrizeRoute Goal) ↔ Goal := by
  constructor
  · rintro ⟨route⟩
    exact route.solve
  · intro hGoal
    exact ⟨{
      certificate := trivialCertificate
      frontier := Goal
      allScalesToFrontier := fun _ => hGoal
      frontierToGoal := fun h => h
    }⟩

theorem six_routes_iff_six_goals
    (A B C D E F : Prop) :
    (Nonempty (PrizeRoute A) ∧
      Nonempty (PrizeRoute B) ∧
      Nonempty (PrizeRoute C) ∧
      Nonempty (PrizeRoute D) ∧
      Nonempty (PrizeRoute E) ∧
      Nonempty (PrizeRoute F)) ↔
    (A ∧ B ∧ C ∧ D ∧ E ∧ F) := by
  simp only [nonempty_prizeRoute_iff]

theorem route_mutual_exclusivity (Goal : Prop) :
    ¬ (Nonempty (PrizeRoute Goal) ∧ ¬ Goal) := by
  rintro ⟨⟨route⟩, hnot⟩
  exact hnot route.solve

noncomputable def haarDensity (d : ℝ) : ℝ := 1 / d ^ 2

noncomputable def inversionJacobian (d : ℝ) : ℝ := 1 / d ^ 4

def inversePointDensity (d : ℝ) : ℝ := d ^ 2

noncomputable def transformedDensity (d : ℝ) : ℝ :=
  inversePointDensity d * inversionJacobian d

theorem transformedDensity_eq_haarDensity
    {d : ℝ} (hd : d ≠ 0) :
    transformedDensity d = haarDensity d := by
  unfold transformedDensity inversePointDensity inversionJacobian haarDensity
  field_simp [hd]

theorem claimed_extra_weight_fails_at_two :
    transformedDensity 2 ≠ haarDensity 2 * haarDensity 2 := by
  norm_num [transformedDensity, inversePointDensity,
    inversionJacobian, haarDensity]

structure ExactObjectFirewall : Prop where
  routeExact : ∀ Goal : Prop, Nonempty (PrizeRoute Goal) ↔ Goal
  sixRouteExact : ∀ A B C D E F : Prop,
    (Nonempty (PrizeRoute A) ∧
      Nonempty (PrizeRoute B) ∧
      Nonempty (PrizeRoute C) ∧
      Nonempty (PrizeRoute D) ∧
      Nonempty (PrizeRoute E) ∧
      Nonempty (PrizeRoute F)) ↔
    (A ∧ B ∧ C ∧ D ∧ E ∧ F)
  routeConsistent : ∀ Goal : Prop,
    ¬ (Nonempty (PrizeRoute Goal) ∧ ¬ Goal)
  haarInversionExact : ∀ {d : ℝ}, d ≠ 0 →
    transformedDensity d = haarDensity d
  extraWeightRefuted :
    transformedDensity 2 ≠ haarDensity 2 * haarDensity 2

theorem exact_object_firewall : ExactObjectFirewall where
  routeExact := nonempty_prizeRoute_iff
  sixRouteExact := six_routes_iff_six_goals
  routeConsistent := route_mutual_exclusivity
  haarInversionExact := transformedDensity_eq_haarDensity
  extraWeightRefuted := claimed_extra_weight_fails_at_two

#print axioms SeventhObject.allScales
#print axioms PrizeRoute.solve
#print axioms nonempty_prizeRoute_iff
#print axioms six_routes_iff_six_goals
#print axioms route_mutual_exclusivity
#print axioms transformedDensity_eq_haarDensity
#print axioms claimed_extra_weight_fails_at_two
#print axioms exact_object_firewall

end MillenniumGrandExactObject
