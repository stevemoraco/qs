universe u

namespace Millennium.B5DualLowerEnvelope

def MonotoneMap {α : Type u} [LE α] (f : α → α) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → f a ≤ f b

def lowerEnvelope {α : Type u}
    (step : Nat → α → α) (initial : α) : Nat → α
  | 0 => initial
  | n + 1 => step n (lowerEnvelope step initial n)

def LowerAdmissible {α : Type u} [LE α]
    (step : Nat → α → α) (initial : α) (d : Nat → α) : Prop :=
  initial ≤ d 0 ∧ ∀ n, step n (d n) ≤ d (n + 1)

theorem lowerEnvelope_le_trajectory
    {α : Type u} [Preorder α]
    (step : Nat → α → α) (initial : α) (d : Nat → α)
    (hmono : ∀ n, MonotoneMap (step n))
    (hd : LowerAdmissible step initial d)
    (n : Nat) :
    lowerEnvelope step initial n ≤ d n := by
  induction n with
  | zero => exact hd.1
  | succ n ih => exact le_trans (hmono n ih) (hd.2 n)

theorem lowerEnvelope_admissible
    {α : Type u} [Preorder α]
    (step : Nat → α → α) (initial : α) :
    LowerAdmissible step initial (lowerEnvelope step initial) := by
  constructor
  · exact le_refl _
  · intro n
    exact le_refl _

theorem terminal_lower_bound_iff_envelope_lower_bound
    {α : Type u} [Preorder α]
    (step : Nat → α → α) (initial : α)
    (hmono : ∀ n, MonotoneMap (step n))
    (terminal : Nat) (bound : α) :
    (∀ d, LowerAdmissible step initial d → bound ≤ d terminal) ↔
      bound ≤ lowerEnvelope step initial terminal := by
  constructor
  · intro h
    exact h (lowerEnvelope step initial)
      (lowerEnvelope_admissible step initial)
  · intro h d hd
    exact le_trans h
      (lowerEnvelope_le_trajectory step initial d hmono hd terminal)

theorem lowerEnvelope_is_greatest_universal_minorant
    {α : Type u} [Preorder α]
    (step : Nat → α → α) (initial : α)
    (hmono : ∀ n, MonotoneMap (step n))
    (minorant : Nat → α) :
    (∀ d, LowerAdmissible step initial d → ∀ n, minorant n ≤ d n) ↔
      ∀ n, minorant n ≤ lowerEnvelope step initial n := by
  constructor
  · intro h
    exact h (lowerEnvelope step initial)
      (lowerEnvelope_admissible step initial)
  · intro h d hd n
    exact le_trans (h n)
      (lowerEnvelope_le_trajectory step initial d hmono hd n)

end Millennium.B5DualLowerEnvelope
