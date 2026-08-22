import Mathlib

namespace PNPLeeCertificateObliviousAlignmentFirewall

/-!
# Finite cores of the certificate-oblivious alignment firewall

A fixed coordinate/head schedule need not identify executions with different
certificate contents.  Separately, local support by possibly different global
histories does not supply one common global witness.

These finite theorems audit two logical inferences in a claimed P=NP route. They
do not decide P versus NP.
-/

/-- A deliberately information-losing coordinate projection: every one-bit
certificate follows the same abstract head coordinate. -/
def fixedCoordinate (_certificate : Bool) : Unit := ()

/-- Two distinct certificate executions can have exactly the same coordinate. -/
theorem distinct_executions_same_fixed_coordinate :
    false ≠ true ∧ fixedCoordinate false = fixedCoordinate true := by
  exact ⟨by decide, rfl⟩

/-- Hence coordinate alignment does not make the coordinate projection
injective. -/
theorem fixed_coordinate_not_injective :
    ¬ Function.Injective fixedCoordinate := by
  intro hinj
  exact Bool.false_ne_true (hinj rfl)

/-- For `m` certificate bits there are `2^m` different contents even when the
coordinate schedule is fixed. -/
theorem certificate_content_count (m : ℕ) :
    Fintype.card (Fin m → Bool) = 2 ^ m := by
  simp

/-- Correlated globally valid two-cell histories. -/
def ValidPair (p : Bool × Bool) : Prop := p.1 = p.2

/-- The first local value `false` has a supporting valid global history. -/
theorem first_false_locally_supported :
    ∃ p : Bool × Bool, ValidPair p ∧ p.1 = false := by
  exact ⟨(false, false), rfl, rfl⟩

/-- The second local value `true` also has a supporting valid global history. -/
theorem second_true_locally_supported :
    ∃ p : Bool × Bool, ValidPair p ∧ p.2 = true := by
  exact ⟨(true, true), rfl, rfl⟩

/-- But splicing those two locally supported values does not give a globally
valid history. -/
theorem locally_supported_splice_globally_invalid :
    (∃ p : Bool × Bool, ValidPair p ∧ p.1 = false) ∧
      (∃ p : Bool × Bool, ValidPair p ∧ p.2 = true) ∧
      ¬ ValidPair (false, true) := by
  exact ⟨first_false_locally_supported,
    second_true_locally_supported, by decide⟩

/-- Smallest quantifier-swap countermodel:
`∀ i, ∃ y, Supports y i` does not imply `∃ y, ∀ i, Supports y i`. -/
theorem forall_exists_does_not_supply_common_witness :
    (∀ i : Bool, ∃ y : Bool, y = i) ∧
      ¬ (∃ y : Bool, ∀ i : Bool, y = i) := by
  constructor
  · intro i
    exact ⟨i, rfl⟩
  · rintro ⟨y, hy⟩
    cases y with
    | false =>
        have h := hy true
        simp at h
    | true =>
        have h := hy false
        simp at h

#print axioms distinct_executions_same_fixed_coordinate
#print axioms fixed_coordinate_not_injective
#print axioms certificate_content_count
#print axioms locally_supported_splice_globally_invalid
#print axioms forall_exists_does_not_supply_common_witness

end PNPLeeCertificateObliviousAlignmentFirewall
