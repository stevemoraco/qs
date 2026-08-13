import Mathlib

namespace MillenniumRun14

/-- A cycle-compatible retraction transfers nonalgebraicity to the lifted class. -/
theorem hodge_cycle_compatible_transfer
    {ZX ZY HX HY : Type*}
    (clX : ZX → HX)
    (clY : ZY → HY)
    (i : HY → HX)
    (p : HX → HY)
    (f : ZX → ZY)
    (alpha : HY)
    (hsection : p (i alpha) = alpha)
    (hcompat : ∀ z, p (clX z) = clY (f z))
    (hnon : alpha ∉ Set.range clY) :
    i alpha ∉ Set.range clX := by
  intro hi
  rcases hi with ⟨z, hz⟩
  apply hnon
  refine ⟨f z, ?_⟩
  calc
    clY (f z) = p (clX z) := (hcompat z).symm
    _ = p (i alpha) := by rw [hz]
    _ = alpha := hsection

end MillenniumRun14
