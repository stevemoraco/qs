import Mathlib

namespace Millennium.BSD.AgyemangCoefficientSpecialization

/-- A three-coordinate toy model for a higher coefficient representation. -/
abbrev HigherClass := ℚ × ℚ × ℚ

/-- A two-coordinate toy model for the ordinary elliptic-curve coefficient representation. -/
abbrev OrdinaryClass := ℚ × ℚ

/-- A concrete coefficient specialization that forgets one higher coordinate. -/
def specialize (v : HigherClass) : OrdinaryClass :=
  (v.1, v.2.1)

/-- A nonzero higher class carried entirely by the forgotten coordinate. -/
def hiddenWitness : HigherClass :=
  (0, 0, 1)

/-- BANKER: a zero-preserving injective specialization really does transfer
nonvanishing from the higher coefficient object to the ordinary one. -/
theorem banker_injective_specialization_transfers_nonzero
    {Higher Ordinary : Type*}
    [Zero Higher] [Zero Ordinary]
    (sp : Higher → Ordinary)
    (hzero : sp 0 = 0)
    (hinj : Function.Injective sp)
    {κ : Higher}
    (hκ : κ ≠ 0) :
    sp κ ≠ 0 := by
  intro hsp
  apply hκ
  apply hinj
  simpa only [hzero] using hsp

/-- CRITIC: merely writing down a coefficient map is not enough.  A nonzero
higher class can lie in its kernel and become zero before the Coleman map is
reached. -/
theorem critic_nonzero_higher_class_can_die_under_specialization :
    hiddenWitness ≠ 0 ∧ specialize hiddenWitness = 0 := by
  constructor
  · intro h
    have hthird := congrArg (fun v : HigherClass => v.2.2) h
    norm_num [hiddenWitness] at hthird
  · rfl

/-- CLEANER: the typed descent closes only after the specific localized class
is proved nonzero after specialization, the Coleman map is proved nonzero on
that image, and an explicit reciprocity law identifies the value with a
nonzero-unit multiple of the target p-adic L-value. -/
theorem cleaner_typed_nonvanishing_requires_all_gates
    {Higher Ordinary Lambda : Type*}
    [Zero Ordinary] [MonoidWithZero Lambda] [IsCancelMulZero Lambda]
    (sp : Higher → Ordinary)
    (col : Ordinary → Lambda)
    (κ : Higher)
    (L u : Lambda)
    (hsp : sp κ ≠ 0)
    (hcol : ∀ x, x ≠ 0 → col x ≠ 0)
    (hrec : col (sp κ) = L * u)
    (hu : u ≠ 0) :
    sp κ ≠ 0 ∧
      col (sp κ) ≠ 0 ∧
      L ≠ 0 ∧
      (col (sp κ) ≠ 0 ↔ L ≠ 0) := by
  have hc : col (sp κ) ≠ 0 := hcol (sp κ) hsp
  have hL : L ≠ 0 := by
    intro hzero
    apply hc
    rw [hrec, hzero, zero_mul]
  have heq : col (sp κ) ≠ 0 ↔ L ≠ 0 := by
    constructor
    · intro hvalue hzero
      apply hvalue
      rw [hrec, hzero, zero_mul]
    · intro htarget
      rw [hrec]
      exact mul_ne_zero htarget hu
  exact ⟨hsp, hc, hL, heq⟩

#print axioms banker_injective_specialization_transfers_nonzero
#print axioms critic_nonzero_higher_class_can_die_under_specialization
#print axioms cleaner_typed_nonvanishing_requires_all_gates

end Millennium.BSD.AgyemangCoefficientSpecialization
