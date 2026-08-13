import Millennium.BSD.FiniteCore

namespace Millennium.Braid.M3

def Certificate : Prop :=
  Millennium.BSD.FiniteCore.fiberDim 1 1 2 = 3 ∧
  Millennium.BSD.FiniteCore.fiberDim 1 1 2 ≠ 4 ∧
  (∃ x : ℝ, x ≠ 0 ∧ Millennium.BSD.FiniteCore.reflection x = -x) ∧
  (∃ x y : ℤ, x ≠ y ∧ x * x = y * y)

theorem core : Certificate := by
  exact ⟨
    Millennium.BSD.FiniteCore.doubleFiberLedger.1,
    Millennium.BSD.FiniteCore.doubleFiberLedger.2,
    Millennium.BSD.FiniteCore.reflected_nonzero_example,
    Millennium.BSD.FiniteCore.square_shadow_not_injective⟩

#print axioms core

end Millennium.Braid.M3
