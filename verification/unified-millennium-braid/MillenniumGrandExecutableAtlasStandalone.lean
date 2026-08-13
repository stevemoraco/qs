import UnifiedMillenniumBraidStandalone

namespace MillenniumGrandExecutableAtlasPublic

open MillenniumBankBackedBraid

def SixOpenTargets (T : TargetInterfaces) : Prop :=
  RiemannHypothesis ∧ T.pNeNP ∧ T.bsd ∧ T.hodge ∧
    T.navierStokes ∧ T.yangMills

def SevenTargetBundle (T : TargetInterfaces) : Prop :=
  SixOpenTargets T ∧ T.poincarePerelman

theorem allTargets_iff_sevenTargetBundle (T : TargetInterfaces) :
    AllTargets T ↔ SevenTargetBundle T := by
  constructor
  · intro h
    exact ⟨⟨h.rh, h.pnp, h.bsd, h.hodge, h.navierStokes, h.yangMills⟩,
      h.poincare⟩
  · intro h
    exact
      { rh := h.1.1
        pnp := h.1.2.1
        bsd := h.1.2.2.1
        hodge := h.1.2.2.2.1
        navierStokes := h.1.2.2.2.2.1
        yangMills := h.1.2.2.2.2.2
        poincare := h.2 }

structure ExactSeventhObject (T : TargetInterfaces) where
  object : Prop
  object_iff_allTargets : object ↔ AllTargets T

theorem MILLENNIUM_GRAND_ATLAS_PUBLIC_EXECUTABLE
    (T : TargetInterfaces)
    (I : ExactSeventhObject T) :
    UnifiedExecutableResult ∧
    (AllTargets T ↔ SevenTargetBundle T) ∧
    (I.object ↔ AllTargets T) ∧
    (I.object ↔ SevenTargetBundle T) ∧
    (I.object → SixOpenTargets T) ∧
    ((¬ SevenTargetBundle T) → ¬ I.object) ∧
    (¬ (∀ A B : Prop, (¬ (A ∧ B)) → A ∨ B)) ∧
    (¬ AllLiveEdges emptyLiveEdges) := by
  refine ⟨unified_millennium_braid_executable, ?_⟩
  refine ⟨allTargets_iff_sevenTargetBundle T, ?_⟩
  refine ⟨I.object_iff_allTargets, ?_⟩
  refine ⟨I.object_iff_allTargets.trans
    (allTargets_iff_sevenTargetBundle T), ?_⟩
  refine ⟨?_, ?_⟩
  · intro hObject
    have hAll : AllTargets T := I.object_iff_allTargets.mp hObject
    exact ⟨hAll.rh, hAll.pnp, hAll.bsd, hAll.hodge,
      hAll.navierStokes, hAll.yangMills⟩
  refine ⟨?_, ?_⟩
  · intro hNotBundle hObject
    exact hNotBundle
      ((I.object_iff_allTargets.trans
        (allTargets_iff_sevenTargetBundle T)).mp hObject)
  exact ⟨mutualExclusivity_does_not_select, emptyLiveEdges_not_closed⟩

#eval IO.println "MILLENNIUM_GRAND_ATLAS_PUBLIC_EXECUTABLE: replay"

#print axioms allTargets_iff_sevenTargetBundle
#print axioms MILLENNIUM_GRAND_ATLAS_PUBLIC_EXECUTABLE

end MillenniumGrandExecutableAtlasPublic
