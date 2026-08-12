import Mathlib

namespace B4Auto10.RH

theorem coerciveCoreMinusTail
    (δ τ energy core tail : ℝ)
    (hcore : δ * energy ≤ core)
    (htail : -(τ * energy) ≤ tail) :
    (δ - τ) * energy ≤ core + tail := by
  linarith

theorem coerciveCoreMinusTailStrict
    (δ τ energy core tail : ℝ)
    (henergy : 0 < energy)
    (hmargin : τ < δ)
    (hcore : δ * energy ≤ core)
    (htail : -(τ * energy) ≤ tail) :
    0 < core + tail := by
  have hbound := coerciveCoreMinusTail δ τ energy core tail hcore htail
  have hpositive : 0 < (δ - τ) * energy :=
    mul_pos (sub_pos.mpr hmargin) henergy
  exact lt_of_lt_of_le hpositive hbound

#print axioms B4Auto10.RH.coerciveCoreMinusTail
#print axioms B4Auto10.RH.coerciveCoreMinusTailStrict

end B4Auto10.RH

namespace B4Auto10.PNP

theorem eliminationBudgetClosesFinitePool
    (initial budget survivors : ℕ)
    (haccount : survivors + budget ≤ initial)
    (hexhaust : initial ≤ budget) :
    survivors = 0 := by
  omega

theorem survivingCircuitForcesBudgetShortfall
    (initial budget survivors : ℕ)
    (haccount : survivors + budget ≤ initial)
    (hsurvivor : 0 < survivors) :
    budget < initial := by
  omega

#print axioms B4Auto10.PNP.eliminationBudgetClosesFinitePool
#print axioms B4Auto10.PNP.survivingCircuitForcesBudgetShortfall

end B4Auto10.PNP

namespace B4Auto10.BSD

def audit235 (n : ℕ) : Prop :=
  ¬ ((2 : ℕ) ∣ n) ∧ ¬ ((3 : ℕ) ∣ n) ∧ ¬ ((5 : ℕ) ∣ n)

theorem audit235_one : audit235 1 := by
  norm_num [audit235]

theorem audit235_seven : audit235 7 := by
  norm_num [audit235]

theorem finitePrimeAuditNotIdentifying :
    ∃ m n : ℕ, m ≠ n ∧ audit235 m ∧ audit235 n := by
  refine ⟨1, 7, ?_, audit235_one, audit235_seven⟩
  norm_num

#print axioms B4Auto10.BSD.audit235_one
#print axioms B4Auto10.BSD.audit235_seven
#print axioms B4Auto10.BSD.finitePrimeAuditNotIdentifying

end B4Auto10.BSD

namespace B4Auto10.Hodge

theorem singleProbeKernelCounterexample :
    Prod.fst ((0, 1) : ℚ × ℚ) = Prod.fst ((0, 0) : ℚ × ℚ) ∧
      ((0, 1) : ℚ × ℚ) ≠ ((0, 0) : ℚ × ℚ) := by
  norm_num

theorem splitAlgebraicityRepair
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (A : Submodule ℚ V) (x projected : V)
    (hprojected : projected ∈ A)
    (hresidual : x - projected ∈ A) :
    x ∈ A := by
  have hsum : (x - projected) + projected ∈ A :=
    A.add_mem hresidual hprojected
  simpa using hsum

#print axioms B4Auto10.Hodge.singleProbeKernelCounterexample
#print axioms B4Auto10.Hodge.splitAlgebraicityRepair

end B4Auto10.Hodge

namespace B4Auto10.NS

theorem escapeCostBudget
    (c escaped cost ε : ℝ)
    (hcost : c * escaped ≤ cost)
    (hbudget : cost ≤ ε) :
    c * escaped ≤ ε :=
  le_trans hcost hbudget

theorem escapeMassBound
    (c escaped cost ε : ℝ)
    (hc : 0 < c)
    (hcost : c * escaped ≤ cost)
    (hbudget : cost ≤ ε) :
    escaped ≤ ε / c := by
  apply (le_div_iff₀ hc).2
  have h := escapeCostBudget c escaped cost ε hcost hbudget
  nlinarith

#print axioms B4Auto10.NS.escapeCostBudget
#print axioms B4Auto10.NS.escapeMassBound

end B4Auto10.NS

namespace B4Auto10.YM

theorem physicalGapScaleTransfer
    (a m g : ℝ)
    (ha : 0 < a)
    (hgap : a * m ≤ g) :
    m ≤ g / a := by
  apply (le_div_iff₀ ha).2
  nlinarith

theorem physicalGapPositive
    (a m g : ℝ)
    (ha : 0 < a)
    (hm : 0 < m)
    (hgap : a * m ≤ g) :
    0 < g / a := by
  exact lt_of_lt_of_le hm (physicalGapScaleTransfer a m g ha hgap)

#print axioms B4Auto10.YM.physicalGapScaleTransfer
#print axioms B4Auto10.YM.physicalGapPositive

end B4Auto10.YM
