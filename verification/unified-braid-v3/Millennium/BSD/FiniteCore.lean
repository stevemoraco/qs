import Mathlib

namespace Millennium.BSD.FiniteCore

def fiberDim (base relative copies : ℕ) : ℕ := base + copies * relative

theorem fiberDim_one_one (r : ℕ) : fiberDim 1 1 r = r + 1 := by
  simp [fiberDim, Nat.add_comm]

theorem doubleFiberLedger : fiberDim 1 1 2 = 3 ∧ fiberDim 1 1 2 ≠ 4 := by
  norm_num [fiberDim]

def reflection (x : ℝ) : ℝ := -x

theorem reflected_nonzero_example :
    ∃ x : ℝ, x ≠ 0 ∧ reflection x = -x := by
  refine ⟨1, by norm_num, ?_⟩
  norm_num [reflection]

theorem square_shadow_not_injective :
    ∃ x y : ℤ, x ≠ y ∧ x * x = y * y := by
  refine ⟨1, -1, by norm_num, by norm_num⟩

#print axioms fiberDim_one_one
#print axioms doubleFiberLedger
#print axioms reflected_nonzero_example
#print axioms square_shadow_not_injective

end Millennium.BSD.FiniteCore
