import Mathlib

namespace HodgeDerivedInvarianceFinite

universe u v

variable {X : Type u} {Y : Type v}

theorem hodge_surjectivity_invariant
    (e : X ≃ Y)
    (HdgX AlgX : X → Prop)
    (HdgY AlgY : Y → Prop)
    (hHdg : ∀ x, HdgX x ↔ HdgY (e x))
    (hAlg : ∀ x, AlgX x ↔ AlgY (e x)) :
    (∀ x, HdgX x → AlgX x) ↔ (∀ y, HdgY y → AlgY y) := by
  constructor
  · intro hX y hy
    let x : X := e.symm y
    have hy' : HdgY (e x) := by simpa [x] using hy
    have hx : HdgX x := (hHdg x).2 hy'
    have ax : AlgX x := hX x hx
    have ay : AlgY (e x) := (hAlg x).1 ax
    simpa [x] using ay
  · intro hY x hx
    have hy : HdgY (e x) := (hHdg x).1 hx
    have ay : AlgY (e x) := hY (e x) hy
    exact (hAlg x).2 ay

theorem predicate_equality_invariant
    (e : X ≃ Y)
    (HdgX AlgX : X → Prop)
    (HdgY AlgY : Y → Prop)
    (hHdg : ∀ x, HdgX x ↔ HdgY (e x))
    (hAlg : ∀ x, AlgX x ↔ AlgY (e x))
    (hX : ∀ x, HdgX x ↔ AlgX x) :
    ∀ y, HdgY y ↔ AlgY y := by
  intro y
  let x : X := e.symm y
  have hxy : e x = y := by simp [x]
  constructor
  · intro hy
    have hxH : HdgX x := by
      apply (hHdg x).2
      simpa [hxy] using hy
    have hxA : AlgX x := (hX x).1 hxH
    have hyA : AlgY (e x) := (hAlg x).1 hxA
    simpa [hxy] using hyA
  · intro hy
    have hxA : AlgX x := by
      apply (hAlg x).2
      simpa [hxy] using hy
    have hxH : HdgX x := (hX x).2 hxA
    have hyH : HdgY (e x) := (hHdg x).1 hxH
    simpa [hxy] using hyH

theorem one_way_map_not_enough :
    let f : Fin 1 → Fin 2 := fun _ => 0
    let HdgX : Fin 1 → Prop := fun _ => True
    let AlgX : Fin 1 → Prop := fun _ => True
    let HdgY : Fin 2 → Prop := fun _ => True
    let AlgY : Fin 2 → Prop := fun y => y = 0
    (∀ x, HdgX x → AlgX x) ∧
    (∀ x, HdgX x → HdgY (f x)) ∧
    (∀ x, AlgX x → AlgY (f x)) ∧
    ¬ (∀ y, HdgY y → AlgY y) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx; trivial
  · intro x hx; trivial
  · intro x hx; rfl
  · intro h
    have hbad : (1 : Fin 2) = 0 := h 1 trivial
    norm_num at hbad

theorem hodge_only_transport_not_enough :
    let e : Fin 2 ≃ Fin 2 := Equiv.refl _
    let HdgX : Fin 2 → Prop := fun _ => True
    let AlgX : Fin 2 → Prop := fun _ => True
    let HdgY : Fin 2 → Prop := fun _ => True
    let AlgY : Fin 2 → Prop := fun y => y = 0
    (∀ x, HdgX x ↔ HdgY (e x)) ∧
    (∀ x, HdgX x → AlgX x) ∧
    ¬ (∀ y, HdgY y → AlgY y) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro x; simp
  · intro x hx; trivial
  · intro h
    have hbad : (1 : Fin 2) = 0 := h 1 trivial
    norm_num at hbad

#print axioms hodge_surjectivity_invariant
#print axioms predicate_equality_invariant
#print axioms one_way_map_not_enough
#print axioms hodge_only_transport_not_enough

end HodgeDerivedInvarianceFinite
