import Mathlib

/-!
# Hodge B4: minimal algebraic-range preservation transfer

Honesty status: abstract set/function logic only. This file does not formalize
algebraic cycles, Hodge structures, smooth projective varieties, correspondences,
or the Hodge conjecture.

It protects the exact logical transfer edge used in the Hodge braid. The
minimal hypothesis is not the existence of an explicit cycle-level lift map;
it is only that the cohomological projection sends algebraic classes to
algebraic classes.
-/

namespace Millennium
namespace HodgeMinimalRangeTransfer

/--
Minimal nonalgebraicity transfer theorem.

If `p` is a left inverse to `i` at the candidate `alpha`, and `p` sends every
class in the source algebraic image into the target algebraic image, then a
nonalgebraic target class remains nonalgebraic after inclusion into the source.
-/
theorem nonalgebraic_transfer_of_range_preservation
    {ZX ZY HX HY : Type*}
    (clX : ZX → HX) (clY : ZY → HY)
    (i : HY → HX) (p : HX → HY)
    (alpha : HY)
    (hsplit : p (i alpha) = alpha)
    (hpreserve : ∀ x, x ∈ Set.range clX → p x ∈ Set.range clY)
    (hnonalg : alpha ∉ Set.range clY) :
    i alpha ∉ Set.range clX := by
  intro halg
  apply hnonalg
  rw [← hsplit]
  exact hpreserve (i alpha) halg

/--
An explicit cycle-compatible map is one sufficient way to obtain the minimal
range-preservation hypothesis.
-/
theorem range_preservation_of_cycle_compatibility
    {ZX ZY HX HY : Type*}
    (clX : ZX → HX) (clY : ZY → HY)
    (p : HX → HY) (f : ZX → ZY)
    (hcompat : ∀ z, p (clX z) = clY (f z)) :
    ∀ x, x ∈ Set.range clX → p x ∈ Set.range clY := by
  intro x hx
  rcases hx with ⟨z, rfl⟩
  exact ⟨f z, (hcompat z).symm⟩

/--
The previously banked cycle-compatible transfer theorem is an immediate
corollary of the cleaner range-preservation statement.
-/
theorem nonalgebraic_transfer_of_cycle_compatibility
    {ZX ZY HX HY : Type*}
    (clX : ZX → HX) (clY : ZY → HY)
    (i : HY → HX) (p : HX → HY) (f : ZX → ZY)
    (alpha : HY)
    (hsplit : p (i alpha) = alpha)
    (hcompat : ∀ z, p (clX z) = clY (f z))
    (hnonalg : alpha ∉ Set.range clY) :
    i alpha ∉ Set.range clX := by
  apply nonalgebraic_transfer_of_range_preservation
    clX clY i p alpha hsplit
  · exact range_preservation_of_cycle_compatibility clX clY p f hcompat
  · exact hnonalg

#print axioms Millennium.HodgeMinimalRangeTransfer.nonalgebraic_transfer_of_range_preservation
#print axioms Millennium.HodgeMinimalRangeTransfer.range_preservation_of_cycle_compatibility
#print axioms Millennium.HodgeMinimalRangeTransfer.nonalgebraic_transfer_of_cycle_compatibility

end HodgeMinimalRangeTransfer
end Millennium
