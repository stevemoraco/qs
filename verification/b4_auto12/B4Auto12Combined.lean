import Mathlib

namespace B4Auto12.RH

theorem cubicStencilZeroMass :
    (1 : ℤ) + (-3) + 3 + (-1) = 0 := by
  norm_num

theorem cubicStencilZeroFirstMoment :
    (0 : ℤ) * 1 + 1 * (-3) + 2 * 3 + 3 * (-1) = 0 := by
  norm_num

theorem cubicStencilZeroSecondMoment :
    (0 : ℤ)^2 * 1 + (1 : ℤ)^2 * (-3) + (2 : ℤ)^2 * 3 + (3 : ℤ)^2 * (-1) = 0 := by
  norm_num

theorem cubicStencilNonzeroThirdMoment :
    (0 : ℤ)^3 * 1 + (1 : ℤ)^3 * (-3) + (2 : ℤ)^3 * 3 + (3 : ℤ)^3 * (-1) = -6 := by
  norm_num

theorem firstThreeMomentsAllowNonzeroSignedResidual :
    (1 : ℤ) ≠ 0 ∧
      (1 : ℤ) + (-3) + 3 + (-1) = 0 ∧
      (0 : ℤ) * 1 + 1 * (-3) + 2 * 3 + 3 * (-1) = 0 ∧
      (0 : ℤ)^2 * 1 + (1 : ℤ)^2 * (-3) + (2 : ℤ)^2 * 3 + (3 : ℤ)^2 * (-1) = 0 := by
  norm_num

#print axioms B4Auto12.RH.cubicStencilZeroMass
#print axioms B4Auto12.RH.cubicStencilZeroFirstMoment
#print axioms B4Auto12.RH.cubicStencilZeroSecondMoment
#print axioms B4Auto12.RH.cubicStencilNonzeroThirdMoment
#print axioms B4Auto12.RH.firstThreeMomentsAllowNonzeroSignedResidual

end B4Auto12.RH

namespace B4Auto12.PNP

theorem twoBadSetsLeaveWitness
    {α : Type*} [DecidableEq α]
    (U B₁ B₂ : Finset α)
    (hsmall : B₁.card + B₂.card < U.card) :
    ∃ x ∈ U, x ∉ B₁ ∧ x ∉ B₂ := by
  by_contra h
  push_neg at h
  have hcover : U ⊆ B₁ ∪ B₂ := by
    intro x hx
    rcases h x hx with hx1 | hx2
    · exact Finset.mem_union_left B₂ hx1
    · exact Finset.mem_union_right B₁ hx2
  have hcardU : U.card ≤ (B₁ ∪ B₂).card := Finset.card_le_card hcover
  have hunion : (B₁ ∪ B₂).card ≤ B₁.card + B₂.card := Finset.card_union_le B₁ B₂
  omega

theorem saturationCanCoverTwoWitnessUniverse :
    let U : Finset (Fin 2) := {0, 1}
    let B₁ : Finset (Fin 2) := {0}
    let B₂ : Finset (Fin 2) := {1}
    B₁.card + B₂.card = U.card ∧
      ∀ x ∈ U, x ∈ B₁ ∨ x ∈ B₂ := by
  norm_num
  intro x hx
  fin_cases x <;> simp

#print axioms B4Auto12.PNP.twoBadSetsLeaveWitness
#print axioms B4Auto12.PNP.saturationCanCoverTwoWitnessUniverse

end B4Auto12.PNP

namespace B4Auto12.BSD

theorem rankSelmerSandwichKillsShaDefect
    (selmer rank sha target : ℕ)
    (hsplit : selmer = rank + sha)
    (hrank : target ≤ rank)
    (hselmer : selmer ≤ target) :
    rank = target ∧ selmer = target ∧ sha = 0 := by
  omega

theorem selmerOneDoesNotForceRankOne :
    ∃ selmer rank sha : ℕ,
      selmer = rank + sha ∧ selmer = 1 ∧ rank = 0 ∧ sha = 1 := by
  exact ⟨1, 0, 1, by norm_num⟩

theorem rankLeSelmer
    (selmer rank sha : ℕ)
    (hsplit : selmer = rank + sha) :
    rank ≤ selmer := by
  omega

#print axioms B4Auto12.BSD.rankSelmerSandwichKillsShaDefect
#print axioms B4Auto12.BSD.selmerOneDoesNotForceRankOne
#print axioms B4Auto12.BSD.rankLeSelmer

end B4Auto12.BSD

namespace B4Auto12.Hodge

theorem rationalSubspaceScalarSaturation
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (A : Submodule ℚ V) (x : V) (q : ℚ)
    (hq : q ≠ 0)
    (hqx : q • x ∈ A) :
    x ∈ A := by
  have hscaled : q⁻¹ • (q • x) ∈ A := A.smul_mem q⁻¹ hqx
  simpa [smul_smul, hq] using hscaled

theorem natMultipleInRationalSubspace
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (A : Submodule ℚ V) (x : V) (n : ℕ)
    (hn : 0 < n)
    (hnx : (n : ℚ) • x ∈ A) :
    x ∈ A := by
  apply rationalSubspaceScalarSaturation A x (n : ℚ)
  · exact_mod_cast Nat.ne_of_gt hn
  · exact hnx

#print axioms B4Auto12.Hodge.rationalSubspaceScalarSaturation
#print axioms B4Auto12.Hodge.natMultipleInRationalSubspace

end B4Auto12.Hodge

namespace B4Auto12.NS

theorem dyadicBudgetLowerBound
    (a : ℕ → ℝ) (N : ℕ) (ε : ℝ)
    (h : ∀ i < N, ε ≤ a i) :
    (N : ℝ) * ε ≤ ∑ i in Finset.range N, a i := by
  have hsum : (∑ _i in Finset.range N, ε) ≤ ∑ i in Finset.range N, a i := by
    exact Finset.sum_le_sum (fun i hi => h i (Finset.mem_range.mp hi))
  simpa using hsum

theorem persistentShellCountBound
    (a : ℕ → ℝ) (N : ℕ) (ε E : ℝ)
    (hε : 0 < ε)
    (hshell : ∀ i < N, ε ≤ a i)
    (hbudget : (∑ i in Finset.range N, a i) ≤ E) :
    (N : ℝ) ≤ E / ε := by
  have hlower := dyadicBudgetLowerBound a N ε hshell
  have htotal : (N : ℝ) * ε ≤ E := le_trans hlower hbudget
  exact (le_div_iff₀ hε).2 htotal

#print axioms B4Auto12.NS.dyadicBudgetLowerBound
#print axioms B4Auto12.NS.persistentShellCountBound

end B4Auto12.NS

namespace B4Auto12.YM

theorem twoSectorConvexGap
    (w g₁ g₂ m : ℝ)
    (hw0 : 0 ≤ w)
    (hw1 : w ≤ 1)
    (hg1 : m ≤ g₁)
    (hg2 : m ≤ g₂) :
    m ≤ w * g₁ + (1 - w) * g₂ := by
  have hleft : 0 ≤ w * (g₁ - m) :=
    mul_nonneg hw0 (sub_nonneg.mpr hg1)
  have hright : 0 ≤ (1 - w) * (g₂ - m) :=
    mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hg2)
  nlinarith

theorem averagedGapDoesNotForceEachSector
    (m : ℝ) (hm : 0 < m) :
    ((1 / 2 : ℝ) * (2 * m) + (1 - (1 / 2 : ℝ)) * 0 = m) ∧
      ¬ m ≤ (0 : ℝ) := by
  constructor
  · ring
  · linarith

#print axioms B4Auto12.YM.twoSectorConvexGap
#print axioms B4Auto12.YM.averagedGapDoesNotForceEachSector

end B4Auto12.YM
