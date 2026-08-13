import Mathlib

namespace Millennium
namespace Round217Hodge

theorem injective_equality_transfer
    {X Y : Type*}
    (f : Y → X)
    (u : Y → Y)
    (hf : Function.Injective f)
    (h : ∀ y : Y, f (u y) = f y) :
    ∀ y : Y, u y = y := by
  intro y
  exact hf (h y)

theorem rational_degree_normalization
    {X : Type*} [AddCommGroup X] [Module ℚ X]
    (n : ℚ) (hn : n ≠ 0) (x : X) :
    (n⁻¹ : ℚ) • (n • x) = x := by
  rw [smul_smul, inv_mul_cancel₀ hn, one_smul]

#print axioms injective_equality_transfer
#print axioms rational_degree_normalization

end Round217Hodge
end Millennium
