import Mathlib

namespace MillenniumBraidUnified
namespace SeventhObjectCore

theorem invariant_margin_tube
    (E : ℕ → ℝ)
    {margin ρ ε : ℝ}
    (hmargin : 0 ≤ margin)
    (hρ : 0 ≤ ρ)
    (hbudget : ρ + ε ≤ 1)
    (h0 : E 0 ≤ margin)
    (hstep : ∀ n : ℕ, E (n + 1) ≤ ρ * E n + ε * margin) :
    ∀ n : ℕ, E n ≤ margin := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
      have hρE : ρ * E n ≤ ρ * margin :=
        mul_le_mul_of_nonneg_left ih hρ
      calc
        E (n + 1) ≤ ρ * E n + ε * margin := hstep n
        _ ≤ ρ * margin + ε * margin := add_le_add_right hρE (ε * margin)
        _ = (ρ + ε) * margin := by ring
        _ ≤ 1 * margin := mul_le_mul_of_nonneg_right hbudget hmargin
        _ = margin := by ring

structure SeventhObject where
  good : ℕ → Prop
  seed : good 0
  propagate : ∀ n : ℕ, good n → good (n + 1)

theorem SeventhObject.all_scales (C : SeventhObject) : ∀ n : ℕ, C.good n := by
  intro n
  induction n with
  | zero => exact C.seed
  | succ n ih => exact C.propagate n ih

structure PrizeRoute (Goal : Prop) where
  certificate : SeventhObject
  frontier : Prop
  all_scales_to_frontier : (∀ n : ℕ, certificate.good n) → frontier
  frontier_to_goal : frontier → Goal

theorem PrizeRoute.solve {Goal : Prop} (R : PrizeRoute Goal) : Goal := by
  exact R.frontier_to_goal
    (R.all_scales_to_frontier R.certificate.all_scales)

def trivialCertificate : SeventhObject where
  good := fun _ => True
  seed := True.intro
  propagate := fun _ _ => True.intro

theorem nonempty_prizeRoute_iff (Goal : Prop) :
    Nonempty (PrizeRoute Goal) ↔ Goal := by
  constructor
  · intro hRoute
    cases hRoute with
    | intro route => exact PrizeRoute.solve route
  · intro hGoal
    exact Nonempty.intro {
      certificate := trivialCertificate
      frontier := Goal
      all_scales_to_frontier := fun _ => hGoal
      frontier_to_goal := fun h => h
    }

end SeventhObjectCore
end MillenniumBraidUnified
