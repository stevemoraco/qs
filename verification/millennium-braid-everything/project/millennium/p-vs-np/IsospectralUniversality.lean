import Mathlib

/-!
# A universal projection chart

For an additive map `B : Y →+ X`, the projection

  `(x,y) ↦ (B y, y)`

is conjugate to the coordinate projection `(x,y) ↦ (0,y)` by the shear
`(x,y) ↦ (x + B y,y)`. Restricting the first input block to zero and taking the
first output block recovers `B` exactly.
-/

namespace PvsNP.IsospectralUniversality

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

/-- The upper-block shear associated with `B`. -/
def shear (B : Y →+ X) : X × Y → X × Y :=
  fun p => (p.1 + B p.2, p.2)

/-- The inverse shear. -/
def unshear (B : Y →+ X) : X × Y → X × Y :=
  fun p => (p.1 - B p.2, p.2)

/-- Coordinate projection onto the second block, retained in graph coordinates. -/
def coordinateProjection : X × Y → X × Y :=
  fun p => (0, p.2)

/-- Projection onto the graph of `B` along the first coordinate block. -/
def graphProjection (B : Y →+ X) : X × Y → X × Y :=
  fun p => (B p.2, p.2)

/-- The two shears cancel in the forward order. -/
theorem shear_unshear (B : Y →+ X) (p : X × Y) :
    shear B (unshear B p) = p := by
  rcases p with ⟨x, y⟩
  simp [shear, unshear]

/-- The two shears cancel in the reverse order. -/
theorem unshear_shear (B : Y →+ X) (p : X × Y) :
    unshear B (shear B p) = p := by
  rcases p with ⟨x, y⟩
  simp [shear, unshear]

/-- Every graph projection is a shear conjugate of the coordinate projection. -/
theorem graphProjection_eq_conjugate
    (B : Y →+ X) (p : X × Y) :
    graphProjection B p =
      shear B (coordinateProjection (unshear B p)) := by
  rcases p with ⟨x, y⟩
  simp [graphProjection, shear, coordinateProjection, unshear]

/-- Graph projections are idempotent. -/
theorem graphProjection_idempotent
    (B : Y →+ X) (p : X × Y) :
    graphProjection B (graphProjection B p) = graphProjection B p := by
  rcases p with ⟨x, y⟩
  rfl

/-- Restricting the first input block to zero recovers `B` in the first output. -/
theorem recover_on_zero_first
    (B : Y →+ X) (y : Y) :
    (graphProjection B (0, y)).1 = B y := by
  rfl

/-- The graph-projection embedding is injective. -/
theorem graphProjection_injective :
    Function.Injective (fun B : Y →+ X => graphProjection B) := by
  intro B C h
  ext y
  have hp := congrFun h (0, y)
  exact congrArg Prod.fst hp

/-- All graph projections have the same kernel: the first coordinate block. -/
theorem graphProjection_eq_zero_iff
    (B : Y →+ X) (p : X × Y) :
    graphProjection B p = (0, 0) ↔ p.2 = 0 := by
  rcases p with ⟨x, y⟩
  simp [graphProjection]

end PvsNP.IsospectralUniversality
