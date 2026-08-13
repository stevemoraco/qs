import Mathlib
namespace B4Auto20Run16

theorem hodge_orbit_invariance
    (G X : Type*) [Group G] [MulAction G X]
    (P : X → Prop)
    (hinv : ∀ g x, P (g • x) ↔ P x)
    (x : X) (hx : P x) : ∀ g : G, P (g • x) := by
  intro g
  exact (hinv g x).2 hx

theorem hodge_no_invariance_counterexample :
    let P : Bool → Prop := fun b => b = false
    let f : Bool → Bool := Bool.not
    P false ∧ ¬ P (f false) := by
  norm_num

theorem hodge_orbit_iff_rep
    (G X : Type*) [Group G] [MulAction G X]
    (P : X → Prop)
    (hinv : ∀ g x, P (g • x) ↔ P x)
    (x : X) : (∀ g : G, P (g • x)) ↔ P x := by
  constructor
  · intro h
    simpa using h (1 : G)
  · intro hx g
    exact (hinv g x).2 hx

#print axioms B4Auto20Run16.hodge_orbit_invariance
#print axioms B4Auto20Run16.hodge_no_invariance_counterexample
#print axioms B4Auto20Run16.hodge_orbit_iff_rep
end B4Auto20Run16
