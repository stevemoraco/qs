import Mathlib

/-!
# P versus NP finite firewall: averaging contrapositive

This file proves only a finite double-counting theorem.  It does not prove
`P = NP` or `P ≠ NP`.

Interpret `errors c x` as the number (normally zero or one) of false accepts
made by deterministic seed `c` on low-ball point `x`.  A uniform pointwise
column bound `q` gives a total error-pair bound.  Equality at the capacity
threshold does not force an error-free seed.  Strict capacity does.
-/

namespace Millennium.PNP.LowBallAveraging

variable {C X : Type*} [Fintype C] [Fintype X]

/-- BANKER: pointwise error counts sum to a global error-pair budget. -/
theorem banker_pointwise_budget_sums
    (errors : C → X → ℕ) (q : ℕ)
    (hPointwise : ∀ x : X, ∑ c : C, errors c x ≤ q) :
    ∑ c : C, ∑ x : X, errors c x ≤ Fintype.card X * q := by
  rw [Finset.sum_comm]
  calc
    (∑ x : X, ∑ c : C, errors c x) ≤ ∑ _x : X, q := by
      exact Finset.sum_le_sum fun x _hx => hPointwise x
    _ = Fintype.card X * q := by simp

/-- CRITIC: at equality, every seed may still make one error. -/
theorem critic_nonstrict_capacity_is_insufficient :
    let errors : Fin 2 → Fin 2 → ℕ := fun c x => if c = x then 1 else 0
    (∀ x : Fin 2, ∑ c : Fin 2, errors c x ≤ 1) ∧
      Fintype.card (Fin 2) * 1 = Fintype.card (Fin 2) ∧
      (∀ c : Fin 2, 0 < ∑ x : Fin 2, errors c x) := by
  dsimp
  constructor
  · intro x
    fin_cases x <;> decide
  constructor
  · decide
  · intro c
    fin_cases c <;> decide

/-- CLEANER: if the total pointwise capacity is strictly smaller than the
number of deterministic seeds, at least one seed has no low-ball errors. -/
theorem cleaner_strict_capacity_yields_zero_error_seed
    (errors : C → X → ℕ) (q : ℕ)
    (hPointwise : ∀ x : X, ∑ c : C, errors c x ≤ q)
    (hCapacity : Fintype.card X * q < Fintype.card C) :
    ∃ c : C, ∑ x : X, errors c x = 0 := by
  have hTotal :
      ∑ c : C, ∑ x : X, errors c x < Fintype.card C :=
    lt_of_le_of_lt
      (banker_pointwise_budget_sums errors q hPointwise)
      hCapacity
  by_contra hNoZero
  push_neg at hNoZero
  have hRows :
      Fintype.card C ≤ ∑ c : C, ∑ x : X, errors c x := by
    calc
      Fintype.card C = ∑ _c : C, 1 := by simp
      _ ≤ ∑ c : C, ∑ x : X, errors c x := by
        exact Finset.sum_le_sum fun c _hc =>
          Nat.one_le_iff_ne_zero.mpr (hNoZero c)
  exact (Nat.not_le_of_lt hTotal) hRows

#print axioms banker_pointwise_budget_sums
#print axioms critic_nonstrict_capacity_is_insufficient
#print axioms cleaner_strict_capacity_yields_zero_error_seed

end Millennium.PNP.LowBallAveraging
