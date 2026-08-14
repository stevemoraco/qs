universe u

namespace Millennium.B5DualLowerEnvelope

theorem reflexive_lower_bound {α : Type u} [Preorder α] (a : α) : a ≤ a := by
  exact le_refl a

end Millennium.B5DualLowerEnvelope
