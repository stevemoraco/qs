import Millennium.Braid.FiniteBank
import Millennium.Braid.ObjectInversion

namespace Millennium.Braid

structure Targets where
  t1 : Prop
  t2 : Prop
  t3 : Prop
  t4 : Prop
  t5 : Prop
  t6 : Prop
  t7 : Prop

def AllTargets (T : Targets) : Prop :=
  T.t1 ∧ T.t2 ∧ T.t3 ∧ T.t4 ∧ T.t5 ∧ T.t6 ∧ T.t7

structure Bridges (T : Targets) where
  b1 : M1.Certificate → T.t1
  b2 : M2.Certificate → T.t2
  b3 : M3.Certificate → T.t3
  b4 : M4.Certificate → T.t4
  b5 : M5.Certificate → T.t5
  b6 : M6.Certificate → T.t6
  b7 : T.t7

theorem allTargets_of_bridges (T : Targets) (B : Bridges T) : AllTargets T := by
  exact ⟨B.b1 finiteBank.lane1,
    B.b2 finiteBank.lane2,
    B.b3 finiteBank.lane3,
    B.b4 finiteBank.lane4,
    B.b5 finiteBank.lane5,
    B.b6 finiteBank.lane6,
    B.b7⟩

def falseFirst : Targets where
  t1 := False
  t2 := True
  t3 := True
  t4 := True
  t5 := True
  t6 := True
  t7 := True

theorem finiteBank_not_universal :
    ¬ (FiniteBank → ∀ T : Targets, AllTargets T) := by
  intro h
  have hall : AllTargets falseFirst := h finiteBank falseFirst
  exact hall.1

theorem bridges_iff_allTargets (T : Targets) :
    Nonempty (Bridges T) ↔ AllTargets T := by
  constructor
  · rintro ⟨B⟩
    exact allTargets_of_bridges T B
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨{
      b1 := fun _ => h1
      b2 := fun _ => h2
      b3 := fun _ => h3
      b4 := fun _ => h4
      b5 := fun _ => h5
      b6 := fun _ => h6
      b7 := h7
    }⟩

#print axioms allTargets_of_bridges
#print axioms finiteBank_not_universal
#print axioms bridges_iff_allTargets

end Millennium.Braid
