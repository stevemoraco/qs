import Mathlib

namespace RHPrimeStaircaseGreen

open Finset

/-- Abstract driven state: one centered forcing impulse advances `z`. -/
structure DrivenState where
  delta : ℕ → ℝ
  z : ℕ → ℝ
  step : ∀ n, z (n + 1) = z n + delta n

/-- The driven state is the cumulative sum of its forcing. -/
theorem z_green (S : DrivenState) :
    ∀ n, S.z n = S.z 0 + ∑ i in range n, S.delta i := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [S.step n, ih]
      simp [sum_range_succ, add_assoc]

/-- Add an energy whose one-step increment is the current logarithmic weight
    times the advanced state. -/
structure DrivenEnergy extends DrivenState where
  L : ℕ → ℝ
  H : ℕ → ℝ
  energy_step : ∀ n, H (n + 1) = H n + L (n + 1) * z (n + 1)

/-- Exact nested-sum Green representation.  This is the finite algebraic core:
    each forcing impulse is integrated once into `z`, then again into `H`. -/
theorem H_green (S : DrivenEnergy) :
    ∀ n,
      S.H n = S.H 0 +
        ∑ j in range n,
          S.L (j + 1) *
            (S.z 0 + ∑ i in range (j + 1), S.delta i) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [S.energy_step n, ih, z_green S.toDrivenState (n + 1)]
      simp [sum_range_succ, add_assoc]

/-- A one-step safety theorem: an adverse work kick cannot cross zero if it is
    smaller in magnitude than the incoming energy margin. -/
theorem positive_after_controlled_adverse_kick
    {H work : ℝ} (hH : 0 < H) (hbudget : -H < work) :
    0 < H + work := by
  linarith

/-- A finite block safety theorem, independent of any prime-specific input. -/
theorem positive_after_block
    {H : ℝ} {work : ℕ → ℝ} {n : ℕ}
    (hH : 0 < H)
    (hbudget : -H < ∑ i in range n, work i) :
    0 < H + ∑ i in range n, work i := by
  linarith

#print axioms z_green
#print axioms H_green
#print axioms positive_after_controlled_adverse_kick
#print axioms positive_after_block

end RHPrimeStaircaseGreen
