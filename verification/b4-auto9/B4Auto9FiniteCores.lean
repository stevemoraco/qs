import Mathlib

namespace B4Auto9.RH

theorem negativeMarginSurvivesTail
    (F κ η main tail : ℝ)
    (hmain : main ≤ -(F * κ))
    (htail : |tail| ≤ η) :
    main + tail ≤ -(F * κ) + η := by
  have htail' : tail ≤ η := le_trans (le_abs_self tail) htail
  linarith

theorem negativeMarginStaysNegative
    (F κ η main tail : ℝ)
    (hmain : main ≤ -(F * κ))
    (htail : |tail| ≤ η)
    (hsep : η < F * κ) :
    main + tail < 0 := by
  have hbound := negativeMarginSurvivesTail F κ η main tail hmain htail
  linarith

#print axioms B4Auto9.RH.negativeMarginSurvivesTail
#print axioms B4Auto9.RH.negativeMarginStaysNegative

end B4Auto9.RH

namespace B4Auto9.PNP

theorem connectedFaninTwoLeafBound
    (gates leaves edges : ℕ)
    (hconnected : gates + leaves ≤ edges + 1)
    (hfanin : edges ≤ 2 * gates) :
    leaves ≤ gates + 1 := by
  omega

theorem cannotExposeSPlusTwoLeaves
    (gates leaves edges : ℕ)
    (hconnected : gates + leaves ≤ edges + 1)
    (hfanin : edges ≤ 2 * gates)
    (hmany : gates + 2 ≤ leaves) : False := by
  have hbound := connectedFaninTwoLeafBound gates leaves edges hconnected hfanin
  omega

#print axioms B4Auto9.PNP.connectedFaninTwoLeafBound
#print axioms B4Auto9.PNP.cannotExposeSPlusTwoLeaves

end B4Auto9.PNP

namespace B4Auto9.BSD

def positiveCount2 (a b : ℕ) : ℕ :=
  (if a = 0 then 0 else 1) + (if b = 0 then 0 else 1)

theorem profilesHaveSameTotalOrder :
    (2 : ℕ) + 0 = 1 + 1 := by
  norm_num

theorem profilesHaveDifferentPositiveCount :
    positiveCount2 2 0 ≠ positiveCount2 1 1 := by
  norm_num [positiveCount2]

theorem noPositiveCountDecoderFromTotalOrder :
    ¬ ∃ f : ℕ → ℕ, ∀ a b : ℕ, f (a + b) = positiveCount2 a b := by
  intro h
  rcases h with ⟨f, hf⟩
  have h20 := hf 2 0
  have h11 := hf 1 1
  norm_num [positiveCount2] at h20 h11
  omega

#print axioms B4Auto9.BSD.profilesHaveSameTotalOrder
#print axioms B4Auto9.BSD.profilesHaveDifferentPositiveCount
#print axioms B4Auto9.BSD.noPositiveCountDecoderFromTotalOrder

end B4Auto9.BSD

namespace B4Auto9.Hodge

theorem cancellationBudget
    (component total cancel target : ℕ)
    (hcomponent : component ≤ total + cancel)
    (htotal : total ≤ target) :
    component ≤ target + cancel := by
  omega

theorem rank22To20NeedsTwoCancellation
    (total cancel : ℕ)
    (hcomponent : 22 ≤ total + cancel)
    (htotal : total ≤ 20) :
    2 ≤ cancel := by
  omega

theorem rankOneCancellationInsufficient
    (total cancel : ℕ)
    (hcomponent : 22 ≤ total + cancel)
    (htotal : total ≤ 20)
    (hcancel : cancel ≤ 1) : False := by
  have htwo := rank22To20NeedsTwoCancellation total cancel hcomponent htotal
  omega

#print axioms B4Auto9.Hodge.cancellationBudget
#print axioms B4Auto9.Hodge.rank22To20NeedsTwoCancellation
#print axioms B4Auto9.Hodge.rankOneCancellationInsufficient

end B4Auto9.Hodge

namespace B4Auto9.NS

theorem criticalSpikeExponentLedger (m : ℤ) :
    (2 * m + m - 4 * m = -m) ∧
    (2 * (2 * m - 1) + m - 4 * m = m - 2) := by
  constructor <;> ring

theorem weakL2SquaredExponentGrows (m : ℤ) (hm : 3 ≤ m) :
    0 < m - 2 := by
  omega

theorem oppositeSpikeScaling (m : ℤ) (hm : 3 ≤ m) :
    -m < 0 ∧ 0 < m - 2 := by
  constructor
  · omega
  · exact weakL2SquaredExponentGrows m hm

#print axioms B4Auto9.NS.criticalSpikeExponentLedger
#print axioms B4Auto9.NS.weakL2SquaredExponentGrows
#print axioms B4Auto9.NS.oppositeSpikeScaling

end B4Auto9.NS

namespace B4Auto9.YM

theorem nonexpansiveProjectionPreservesApproximation
    {α : Type*} [PseudoMetricSpace α]
    (P : α → α) (x y : α) (ε : ℝ)
    (hy : P y = y)
    (hcontract : dist (P x) (P y) ≤ dist x y)
    (happrox : dist x y ≤ ε) :
    dist (P x) y ≤ ε := by
  rw [← hy]
  exact hcontract.trans happrox

theorem projectedWitness
    {α : Type*} [PseudoMetricSpace α]
    (P : α → α) (y : α)
    (hy : P y = y)
    (ε : ℝ)
    (x : α)
    (hcontract : dist (P x) (P y) ≤ dist x y)
    (happrox : dist x y ≤ ε) :
    ∃ z : α, z = P x ∧ dist z y ≤ ε := by
  refine ⟨P x, rfl, ?_⟩
  exact nonexpansiveProjectionPreservesApproximation P x y ε hy hcontract happrox

#print axioms B4Auto9.YM.nonexpansiveProjectionPreservesApproximation
#print axioms B4Auto9.YM.projectedWitness

end B4Auto9.YM
