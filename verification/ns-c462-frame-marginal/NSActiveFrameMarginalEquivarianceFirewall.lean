import Mathlib

namespace Millennium.NavierStokes.C462

inductive Phase3 where
  | p0 | p1 | p2
  deriving DecidableEq, Fintype

open Phase3

def rotate : Phase3 → Phase3
  | p0 => p1
  | p1 => p2
  | p2 => p0

def physical : Phase3 → Phase3 := id

def scrambled : Phase3 → Phase3
  | p0 => p0
  | p1 => p2
  | p2 => p1

def scrambleEquiv : Phase3 ≃ Phase3 where
  toFun := scrambled
  invFun := scrambled
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x <;> rfl

def fiberCount (h : Phase3 → Phase3) (y : Phase3) : ℕ :=
  (Finset.univ.filter fun x => h x = y).card

theorem same_orientation_marginal (y : Phase3) :
    fiberCount physical y = fiberCount scrambled y := by
  cases y <;> decide

theorem scrambled_full_support (y : Phase3) :
    ∃ x, scrambled x = y :=
  scrambleEquiv.surjective y

theorem physical_equivariant :
    ∀ x, physical (rotate x) = rotate (physical x) := by
  intro x
  cases x <;> rfl

theorem scrambled_not_equivariant :
    ¬ ∀ x, scrambled (rotate x) = rotate (scrambled x) := by
  intro h
  have h0 := h p0
  cases h0

theorem marginal_does_not_determine_equivariance :
    (∀ y, fiberCount physical y = fiberCount scrambled y) ∧
    (∀ y, ∃ x, scrambled x = y) ∧
    (∀ x, physical (rotate x) = rotate (physical x)) ∧
    ¬ (∀ x, scrambled (rotate x) = rotate (scrambled x)) := by
  exact ⟨same_orientation_marginal, scrambled_full_support,
    physical_equivariant, scrambled_not_equivariant⟩

theorem equivariant_field_is_translate
    {G : Type*} [AddGroup G] (h : G → G)
    (heq : ∀ x a, h (x + a) = h x + a) :
    ∀ x, h x = h 0 + x := by
  intro x
  simpa using heq 0 x

theorem anchored_equivariant_field_is_identity
    {G : Type*} [AddGroup G] (h : G → G)
    (heq : ∀ x a, h (x + a) = h x + a)
    (h0 : h 0 = 0) :
    ∀ x, h x = x := by
  intro x
  rw [equivariant_field_is_translate h heq x, h0, zero_add]

#print axioms same_orientation_marginal
#print axioms scrambled_full_support
#print axioms physical_equivariant
#print axioms scrambled_not_equivariant
#print axioms marginal_does_not_determine_equivariance
#print axioms equivariant_field_is_translate
#print axioms anchored_equivariant_field_is_identity

end Millennium.NavierStokes.C462
