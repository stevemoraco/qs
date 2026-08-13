import Millennium.Braid.Targets

namespace Millennium.Braid

structure GrandBank : Prop where
  finite : FiniteBank
  quantifiers : QuantifierCertificate
  lowerTransferField : ∀ {a b e m : ℝ},
    |a - b| ≤ e → m + e ≤ b → m ≤ a
  upperTransferField : ∀ {a b e u : ℝ},
    |a - b| ≤ e → b + e ≤ u → a ≤ u
  noDual : ∀ P : Prop, ¬ (P ∧ ¬ P)
  noExhaustivityFromNoDual :
    ¬ ((∀ P : Prop, ¬ (P ∧ ¬ P)) → ∀ P : Prop, P)
  bridgeStrength : ∀ T : Targets, Nonempty (Bridges T) ↔ AllTargets T
  boundary : ¬ (FiniteBank → ∀ T : Targets, AllTargets T)

theorem grandUnifiedStatement : GrandBank := by
  exact {
    finite := finiteBank
    quantifiers := quantifierCertificate
    lowerTransferField := fun h1 h2 => lowerTransfer h1 h2
    upperTransferField := fun h1 h2 => upperTransfer h1 h2
    noDual := noBoth
    noExhaustivityFromNoDual := noncontradiction_not_everything
    bridgeStrength := bridges_iff_allTargets
    boundary := finiteBank_not_universal
  }

#print axioms grandUnifiedStatement

end Millennium.Braid
