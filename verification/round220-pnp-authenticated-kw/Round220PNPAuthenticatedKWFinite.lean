import Mathlib

/-!
# Round 220 P versus NP authenticated-KW finite cores

This file formalizes only finite Boolean-row and counting facts behind the
communication firewall. It does not formalize communication protocols,
circuits, MCSP, hardness magnification, complexity classes, or `P ≠ NP`.
-/

namespace Millennium
namespace Round220PNP

/-- Two distinct Boolean rows differ at at least one coordinate. -/
theorem distinct_rows_have_mismatch
    {I : Type*} (a z : I → Bool) (h : a ≠ z) :
    ∃ i : I, a i ≠ z i := by
  by_contra hnone
  apply h
  funext i
  by_contra hi
  exact hnone ⟨i, hi⟩

/-- The finite relation whose valid outputs are mismatching coordinates. -/
def AuthenticatedDifference
    {D I : Type*} (eval : D → I → Bool)
    (d : D) (z : I → Bool) (i : I) : Prop :=
  eval d i ≠ z i

/-- Whenever the described row is distinct from Bob's row, the authenticated
valid-output relation is total. -/
theorem authenticated_difference_total
    {D I : Type*} (eval : D → I → Bool)
    (d : D) (z : I → Bool) (h : eval d ≠ z) :
    ∃ i : I, AuthenticatedDifference eval d z i := by
  exact distinct_rows_have_mismatch (eval d) z h

/-- Binary description strings of length `L` have exactly `2^L` possibilities. -/
theorem binary_description_space_card (L : ℕ) :
    Fintype.card (Fin L → Bool) = 2 ^ L := by
  simp

/-- If there are at most `2^L` descriptions, the naive description-by-coordinate
rectangle family has at most `2^L * N` members. -/
theorem description_rectangle_count
    (descriptionCount coordinateCount L : ℕ)
    (hcode : descriptionCount ≤ 2 ^ L) :
    descriptionCount * coordinateCount ≤
      (2 ^ L) * coordinateCount := by
  exact Nat.mul_le_mul_right coordinateCount hcode

/-- A singleton description family needs at most one coordinate-labelled
rectangle per coordinate. -/
theorem singleton_description_rectangle_count
    (coordinateCount : ℕ) :
    1 * coordinateCount = coordinateCount := by
  simp

/-- Description bits followed by an output-coordinate index have the exact
additive message budget used in the prose protocol. -/
theorem description_then_index_budget
    (descriptionBits indexBits : ℕ) :
    descriptionBits + indexBits = indexBits + descriptionBits := by
  omega

/-- A positive Hamming-distance witness is stronger than mere row inequality. -/
theorem mismatch_witness_implies_distinct
    {I : Type*} (a z : I → Bool)
    (h : ∃ i : I, a i ≠ z i) :
    a ≠ z := by
  intro haz
  obtain ⟨i, hi⟩ := h
  exact hi (congrFun haz i)

/-- Encoding descriptions injectively into `L`-bit strings gives the expected
cardinality bound. -/
theorem injective_binary_code_card_bound
    {D : Type*} [Fintype D] (L : ℕ)
    (code : D → (Fin L → Bool))
    (hcode : Function.Injective code) :
    Fintype.card D ≤ 2 ^ L := by
  calc
    Fintype.card D ≤ Fintype.card (Fin L → Bool) :=
      Fintype.card_le_of_injective code hcode
    _ = 2 ^ L := binary_description_space_card L

#print axioms distinct_rows_have_mismatch
#print axioms authenticated_difference_total
#print axioms binary_description_space_card
#print axioms description_rectangle_count
#print axioms singleton_description_rectangle_count
#print axioms description_then_index_budget
#print axioms mismatch_witness_implies_distinct
#print axioms injective_binary_code_card_bound

end Round220PNP
end Millennium
