import Mathlib

/-!
# Nonlinear graph projections by shear conjugacy

For an arbitrary function `g : Y → X` into an additive group, the map

  `(x,y) ↦ (g y,y)`

is an idempotent conjugate of the coordinate projection `(x,y) ↦ (0,y)` by the
possibly nonlinear shear `(x,y) ↦ (x + g y,y)`. Restricting to a zero first
input recovers `g` exactly.
-/

namespace PvsNP.NonlinearProjectionUniversality

variable {X Y : Type*} [AddCommGroup X]

/-- Nonlinear shear associated with an arbitrary function `g`. -/
def shear (g : Y → X) : X × Y → X × Y :=
  fun p => (p.1 + g p.2, p.2)

/-- Inverse nonlinear shear. -/
def unshear (g : Y → X) : X × Y → X × Y :=
  fun p => (p.1 - g p.2, p.2)

/-- Coordinate projection onto the second block. -/
def coordinateProjection : X × Y → X × Y :=
  fun p => (0, p.2)

/-- Projection onto the graph of `g`. -/
def graphProjection (g : Y → X) : X × Y → X × Y :=
  fun p => (g p.2, p.2)

/-- Forward shear after inverse shear is the identity. -/
theorem shear_unshear (g : Y → X) (p : X × Y) :
    shear g (unshear g p) = p := by
  rcases p with ⟨x, y⟩
  simp [shear, unshear]

/-- Inverse shear after forward shear is the identity. -/
theorem unshear_shear (g : Y → X) (p : X × Y) :
    unshear g (shear g p) = p := by
  rcases p with ⟨x, y⟩
  simp [shear, unshear]

/-- Graph projection is the shear conjugate of coordinate projection. -/
theorem graphProjection_eq_conjugate (g : Y → X) (p : X × Y) :
    graphProjection g p =
      shear g (coordinateProjection (unshear g p)) := by
  rcases p with ⟨x, y⟩
  simp [graphProjection, shear, coordinateProjection, unshear]

/-- Every graph projection is idempotent. -/
theorem graphProjection_idempotent (g : Y → X) (p : X × Y) :
    graphProjection g (graphProjection g p) = graphProjection g p := by
  rcases p with ⟨x, y⟩
  rfl

/-- Restricting the first input to zero recovers the arbitrary function `g`. -/
theorem recover_on_zero_first (g : Y → X) (y : Y) :
    (graphProjection g (0, y)).1 = g y := by
  rfl

/-- The graph-projection construction is injective in `g`. -/
theorem graphProjection_injective :
    Function.Injective (fun g : Y → X => graphProjection g) := by
  intro g h hEq
  funext y
  have hp := congrFun hEq (0, y)
  exact congrArg Prod.fst hp

/-- The image consists exactly of graph points. -/
theorem mem_range_graphProjection_iff (g : Y → X) (p : X × Y) :
    p ∈ Set.range (graphProjection g) ↔ p.1 = g p.2 := by
  constructor
  · rintro ⟨q, rfl⟩
    rfl
  · intro hp
    refine ⟨(0, p.2), ?_⟩
    rcases p with ⟨x, y⟩
    simp [graphProjection] at hp ⊢
    exact hp.symm

end PvsNP.NonlinearProjectionUniversality
