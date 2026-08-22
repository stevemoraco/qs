import Mathlib

namespace BSDCMGoldfeldClosureCore

structure TwistData (α : Type) where
  selmerRank : α → ℕ
  analyticRank : α → ℕ
  mwRank : α → ℕ
  shaFinite : α → Prop
  strongBSD : α → Prop

theorem lowSelmerClosesQualitativeBSD
    {α : Type}
    (D : TwistData α)
    (hConverse0 : ∀ x, D.selmerRank x = 0 → D.analyticRank x = 0)
    (hConverse1 : ∀ x, D.selmerRank x = 1 → D.analyticRank x = 1)
    (hForward : ∀ x, D.analyticRank x ≤ 1 →
      D.mwRank x = D.analyticRank x ∧ D.shaFinite x) :
    ∀ x, D.selmerRank x ≤ 1 →
      D.mwRank x = D.analyticRank x ∧ D.shaFinite x := by
  intro x hx
  interval_cases h : D.selmerRank x
  · have ha : D.analyticRank x = 0 := hConverse0 x h
    exact hForward x (by omega)
  · have ha : D.analyticRank x = 1 := hConverse1 x h
    exact hForward x (by omega)

theorem zeroPacketClosesStrongBSD
    {α : Type}
    (D : TwistData α)
    (hConverse0 : ∀ x, D.selmerRank x = 0 → D.analyticRank x = 0)
    (hStrong0 : ∀ x, D.analyticRank x = 0 → D.strongBSD x) :
    ∀ x, D.selmerRank x = 0 → D.strongBSD x := by
  intro x hx
  exact hStrong0 x (hConverse0 x hx)

theorem finiteSampleQualitativeClosure
    {α : Type}
    [DecidableEq α]
    (S : Finset α)
    (D : TwistData α)
    [DecidablePred D.shaFinite]
    (hPackets : ∀ x ∈ S, D.selmerRank x ≤ 1)
    (hConverse0 : ∀ x, D.selmerRank x = 0 → D.analyticRank x = 0)
    (hConverse1 : ∀ x, D.selmerRank x = 1 → D.analyticRank x = 1)
    (hForward : ∀ x, D.analyticRank x ≤ 1 →
      D.mwRank x = D.analyticRank x ∧ D.shaFinite x) :
    (S.filter fun x =>
      D.mwRank x = D.analyticRank x ∧ D.shaFinite x).card = S.card := by
  have hAll : S.filter (fun x =>
      D.mwRank x = D.analyticRank x ∧ D.shaFinite x) = S := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, lowSelmerClosesQualitativeBSD D hConverse0 hConverse1 hForward x
        (hPackets x hx)⟩
  rw [hAll]

theorem rankOneIsOnlyLowRankStrongFrontier
    {α : Type}
    (D : TwistData α)
    (hStrong0 : ∀ x, D.analyticRank x = 0 → D.strongBSD x)
    (x : α)
    (hLow : D.analyticRank x ≤ 1)
    (hNotStrong : ¬ D.strongBSD x) :
    D.analyticRank x = 1 := by
  have hNotZero : D.analyticRank x ≠ 0 := by
    intro hZero
    exact hNotStrong (hStrong0 x hZero)
  omega

#print axioms lowSelmerClosesQualitativeBSD
#print axioms zeroPacketClosesStrongBSD
#print axioms finiteSampleQualitativeClosure
#print axioms rankOneIsOnlyLowRankStrongFrontier

end BSDCMGoldfeldClosureCore
