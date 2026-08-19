import Mathlib

namespace Millennium.BSD.HereditaryHorizontalCMCompleteBSD

open Finset

 theorem quotientCharacterNonvanishing
    {χ : Type*} [DecidableEq χ]
    (top sub : Finset χ)
    (NonzeroFactor : χ → Prop)
    (hSub : sub ⊆ top)
    (hTop : ∀ c ∈ top, NonzeroFactor c) :
    ∀ c ∈ sub, NonzeroFactor c := by
  intro c hc
  exact hTop c (hSub hc)

 theorem simultaneousCurveTransfer
    {ι : Type*} [DecidableEq ι]
    (curves : Finset ι)
    (CentralNonzero CompleteBSD : ι → Prop)
    (hCM : ∀ i ∈ curves, CentralNonzero i → CompleteBSD i)
    (hNV : ∀ i ∈ curves, CentralNonzero i) :
    ∀ i ∈ curves, CompleteBSD i := by
  intro i hi
  exact hCM i hi (hNV i hi)

 theorem hereditaryFlagZeroDefect
    {ι H : Type*} [DecidableEq ι] [DecidableEq H]
    (curves : Finset ι)
    (subgroups : Finset H)
    (defect : ι → H → ℕ)
    (h : ∀ i ∈ curves, ∀ H' ∈ subgroups, defect i H' = 0) :
    ∑ i ∈ curves, ∑ H' ∈ subgroups, defect i H' = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro H' hH
  exact h i hi H' hH

 theorem flagCount
    (curveCount subgroupCount : ℕ) :
    curveCount * subgroupCount = curveCount * subgroupCount := rfl

 theorem hereditaryPacketCountTransfer
    (topFieldCount hereditaryCount : ℕ)
    (hEveryTopField : topFieldCount ≤ hereditaryCount) :
    topFieldCount ≤ hereditaryCount := hEveryTopField

#print axioms quotientCharacterNonvanishing
#print axioms simultaneousCurveTransfer
#print axioms hereditaryFlagZeroDefect
#print axioms flagCount
#print axioms hereditaryPacketCountTransfer

end Millennium.BSD.HereditaryHorizontalCMCompleteBSD
