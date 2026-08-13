import Mathlib

namespace SixLaneAudit.HodgeF4TrigonalObstruction

/--
Abstract finite core of the `F₄` trigonal obstruction.

After the geometric reductions, `branchBase` is the source ruling restricted to
its moving genus-10 branch curve, `targetBase` is the target ruling after
identifying the two moving branch curves, and `τ` is the base automorphism
forced by uniqueness of the trigonal pencil. The three points `x` lie on one
general source ruling fibre. The ruling-to-section property makes their target
base values injective, while trigonal uniqueness makes all three values equal.
-/
theorem trigonal_fiber_collision
    {C SourceBase TargetBase : Type*}
    (branchBase : C → SourceBase)
    (targetBase : C → TargetBase)
    (τ : SourceBase → TargetBase)
    (x : Fin 3 → C)
    (u : SourceBase)
    (h_same_source_fiber : ∀ i, branchBase (x i) = u)
    (h_trigonal_unique : ∀ p, targetBase p = τ (branchBase p))
    (h_target_base_injective : Function.Injective (fun i => targetBase (x i))) :
    False := by
  have h01 : targetBase (x 0) = targetBase (x 1) := by
    rw [h_trigonal_unique (x 0), h_trigonal_unique (x 1),
      h_same_source_fiber 0, h_same_source_fiber 1]
  have hfin : (0 : Fin 3) = 1 := h_target_base_injective h01
  norm_num at hfin

#print axioms trigonal_fiber_collision

end SixLaneAudit.HodgeF4TrigonalObstruction
