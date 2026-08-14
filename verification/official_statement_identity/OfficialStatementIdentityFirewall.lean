import Mathlib

namespace Millennium.OfficialStatementIdentity

structure TargetBundle where
  rh : Prop
  pnp : Prop
  bsd : Prop
  hodge : Prop
  ns : Prop
  ym : Prop
  poincare : Prop
  inversion : Prop

def All (T : TargetBundle) : Prop :=
  T.rh ∧ T.pnp ∧ T.bsd ∧ T.hodge ∧ T.ns ∧ T.ym ∧ T.poincare ∧ T.inversion

structure IdentityCertificate (abstract official : TargetBundle) : Prop where
  rh : abstract.rh ↔ official.rh
  pnp : abstract.pnp ↔ official.pnp
  bsd : abstract.bsd ↔ official.bsd
  hodge : abstract.hodge ↔ official.hodge
  ns : abstract.ns ↔ official.ns
  ym : abstract.ym ↔ official.ym
  poincare : abstract.poincare ↔ official.poincare
  inversion : abstract.inversion ↔ official.inversion

theorem all_iff_of_identity_certificate
    {abstract official : TargetBundle}
    (c : IdentityCertificate abstract official) :
    All abstract ↔ All official := by
  constructor
  · rintro ⟨hrh, hpnp, hbsd, hhodge, hns, hym, hpoincare, hinversion⟩
    exact ⟨c.rh.mp hrh, c.pnp.mp hpnp, c.bsd.mp hbsd, c.hodge.mp hhodge,
      c.ns.mp hns, c.ym.mp hym, c.poincare.mp hpoincare,
      c.inversion.mp hinversion⟩
  · rintro ⟨hrh, hpnp, hbsd, hhodge, hns, hym, hpoincare, hinversion⟩
    exact ⟨c.rh.mpr hrh, c.pnp.mpr hpnp, c.bsd.mpr hbsd,
      c.hodge.mpr hhodge, c.ns.mpr hns, c.ym.mpr hym,
      c.poincare.mpr hpoincare, c.inversion.mpr hinversion⟩

theorem abstract_labels_do_not_imply_official_targets :
    ∃ abstract official : TargetBundle,
      All abstract ∧ ¬ All official := by
  let abstract : TargetBundle :=
    { rh := True, pnp := True, bsd := True, hodge := True,
      ns := True, ym := True, poincare := True, inversion := True }
  let official : TargetBundle :=
    { rh := False, pnp := True, bsd := True, hodge := True,
      ns := True, ym := True, poincare := True, inversion := True }
  refine ⟨abstract, official, ?_, ?_⟩
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  · intro h
    exact h.1

structure CompletionRoute (Goal : Prop) : Prop where
  close : Goal

theorem completionRoute_nonempty_iff (Goal : Prop) :
    Nonempty (CompletionRoute Goal) ↔ Goal := by
  constructor
  · rintro ⟨route⟩
    exact route.close
  · intro h
    exact ⟨⟨h⟩⟩

theorem exclusivity_without_coverage_counterexample :
    ∃ P Q : Prop, ¬ (P ∧ Q) ∧ ¬ P ∧ ¬ Q := by
  exact ⟨False, False, by simp⟩

#print axioms Millennium.OfficialStatementIdentity.all_iff_of_identity_certificate
#print axioms Millennium.OfficialStatementIdentity.abstract_labels_do_not_imply_official_targets
#print axioms Millennium.OfficialStatementIdentity.completionRoute_nonempty_iff
#print axioms Millennium.OfficialStatementIdentity.exclusivity_without_coverage_counterexample

end Millennium.OfficialStatementIdentity
