import Mathlib

/-!
# Round 215 BSD source-interface finite cores

This file formalizes only elementary valuation-index and type-transport
firewalls. It does not formalize elliptic curves, Selmer complexes,
determinant functors, Hida families, Euler/Kolyvagin/Stark systems,
characteristic ideals, or the Birch--Swinnerton-Dyer conjecture.
-/

namespace Millennium
namespace Round215BSD

/-- Equality of rank-one DVR lattices is represented by equality of their
valuation exponents. -/
def SameLatticeExponent (a b : ℕ) : Prop := a = b

/-- A single ideal divisibility permits an arbitrarily large strict index gap. -/
theorem one_divisibility_allows_arbitrary_gap
    (d : ℕ) (hd : 0 < d) :
    0 ≤ d ∧ ¬ SameLatticeExponent 0 d := by
  constructor
  · exact Nat.zero_le d
  · simpa [SameLatticeExponent] using (Nat.ne_of_gt hd).symm

/-- The opposite one-sided divisibility also permits an arbitrary strict gap. -/
theorem reverse_divisibility_allows_arbitrary_gap
    (d : ℕ) (hd : 0 < d) :
    0 ≤ d ∧ ¬ SameLatticeExponent d 0 := by
  constructor
  · exact Nat.zero_le d
  · simpa [SameLatticeExponent] using Nat.ne_of_gt hd

/-- Two opposite valuation inequalities force equality of the two integral
rank-one lattices. -/
theorem two_divisibilities_exactify
    (a b : ℕ) (hab : a ≤ b) (hba : b ≤ a) :
    SameLatticeExponent a b := by
  exact Nat.le_antisymm hab hba

/-- An equivalence from determinant data to Stark data transports an element
that is already present on the determinant side. -/
theorem determinant_to_stark_transports_existing
    {D S : Type*} (equiv : D ≃ S) (d : D) :
    ∃ s : S, s = equiv d := by
  exact ⟨equiv d, rfl⟩

/-- Transport through an equivalence preserves an explicitly supplied marked
property when that preservation theorem is one of the hypotheses. -/
theorem determinant_to_stark_preserves_supplied_property
    {D S : Type*} (equiv : D ≃ S)
    (goodD : D → Prop) (goodS : S → Prop)
    (hpreserve : ∀ d, goodD d → goodS (equiv d))
    (d : D) (hd : goodD d) :
    goodS (equiv d) := by
  exact hpreserve d hd

/-- An unrelated source element can exist while a proposed conversion sends it
to an object lacking the desired determinant-basis property. This finite
countermodel protects the missing bridge from being hidden by shared naming. -/
def SourceGood (_ : Unit) : Prop := True

def DeterminantBasis (b : Bool) : Prop := b = true

def UnrelatedConversion (_ : Unit) : Bool := false

theorem unrelated_source_does_not_supply_basis :
    SourceGood () ∧ ¬ DeterminantBasis (UnrelatedConversion ()) := by
  constructor
  · trivial
  · simp [DeterminantBasis, UnrelatedConversion]

/-- In the scalar index model, exact basis status is precisely zero residual
index. -/
theorem zero_residual_index_iff_basis (d : ℕ) :
    SameLatticeExponent 0 d ↔ d = 0 := by
  simp [SameLatticeExponent]

#print axioms one_divisibility_allows_arbitrary_gap
#print axioms reverse_divisibility_allows_arbitrary_gap
#print axioms two_divisibilities_exactify
#print axioms determinant_to_stark_transports_existing
#print axioms determinant_to_stark_preserves_supplied_property
#print axioms unrelated_source_does_not_supply_basis
#print axioms zero_residual_index_iff_basis

end Round215BSD
end Millennium
