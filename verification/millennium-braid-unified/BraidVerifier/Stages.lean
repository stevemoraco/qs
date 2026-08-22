import Mathlib

namespace BraidVerifier.Stages

structure Flow where
  good : Nat → Prop
  seed : good 0
  step : ∀ n : Nat, good n → good (n + 1)

theorem all (F : Flow) : ∀ n : Nat, F.good n := by
  intro n
  induction n with
  | zero => exact F.seed
  | succ n ih => exact F.step n ih

end BraidVerifier.Stages
