import Mathlib

namespace Run16AxiomProbe

theorem generic_add_comm
    {α : Type*} [AddCommMonoid α] (a b : α) : a + b = b + a :=
  add_comm a b

theorem nat_add_comm (a b : ℕ) : a + b = b + a :=
  Nat.add_comm a b

theorem int_add_comm (a b : ℤ) : a + b = b + a :=
  Int.add_comm a b

theorem real_add_comm (a b : ℝ) : a + b = b + a :=
  add_comm a b

theorem generic_ring_identity
    {α : Type*} [CommRing α] (a b : α) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

theorem int_ring_identity (a b : ℤ) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

theorem real_ring_identity (a b : ℝ) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

theorem generic_sq_nonneg
    {α : Type*} [LinearOrderedRing α] (a : α) : 0 ≤ a ^ 2 := by
  exact sq_nonneg a

theorem real_sq_nonneg (a : ℝ) : 0 ≤ a ^ 2 := by
  exact sq_nonneg a

#print axioms Run16AxiomProbe.generic_add_comm
#print axioms Run16AxiomProbe.nat_add_comm
#print axioms Run16AxiomProbe.int_add_comm
#print axioms Run16AxiomProbe.real_add_comm
#print axioms Run16AxiomProbe.generic_ring_identity
#print axioms Run16AxiomProbe.int_ring_identity
#print axioms Run16AxiomProbe.real_ring_identity
#print axioms Run16AxiomProbe.generic_sq_nonneg
#print axioms Run16AxiomProbe.real_sq_nonneg

end Run16AxiomProbe
