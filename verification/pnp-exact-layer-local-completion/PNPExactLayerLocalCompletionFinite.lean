import Mathlib

namespace PNPExactLayerLocalCompletionFinite

/-- The local four-shell promise has values `0,0,1,0` at weights
    `0,1,2,3`.  Positive-even is one total completion. -/
theorem positiveEven_agrees_on_four_shells
    (w : ℕ) (hw : w ≤ 3) :
    (0 < w ∧ w % 2 = 0) ↔ w = 2 := by
  omega

/-- The elementary gate budget for the positive-even completion. -/
theorem positiveEven_gate_budget
    (r : ℕ) (hr : 1 ≤ r) :
    (r - 1) + (r - 1) + 1 = 2 * r - 1 := by
  omega

private def nor (a b : Bool) : Bool := !(a || b)
private def lt (a b : Bool) : Bool := (!a) && b
private def xnor (a b : Bool) : Bool := !(Bool.xor a b)

private def bit (b : Bool) : ℕ := if b = true then 1 else 0

private def weight4 (x0 x1 x2 x3 : Bool) : ℕ :=
  bit x0 + bit x1 + bit x2 + bit x3

private def weight5 (x0 x1 x2 x3 x4 : Bool) : ℕ :=
  bit x0 + bit x1 + bit x2 + bit x3 + bit x4

private def positiveEven4 (x0 x1 x2 x3 : Bool) : Bool :=
  decide (0 < weight4 x0 x1 x2 x3 ∧ weight4 x0 x1 x2 x3 % 2 = 0)

private def positiveEven5 (x0 x1 x2 x3 x4 : Bool) : Bool :=
  decide (0 < weight5 x0 x1 x2 x3 x4 ∧ weight5 x0 x1 x2 x3 x4 % 2 = 0)

/-- Six-gate full-binary-basis circuit discovered by the hostile finite search. -/
private def h4 (x0 x1 x2 x3 : Bool) : Bool :=
  let g0 := nor x0 x1
  let g1 := lt x2 g0
  let g2 := nor x3 g1
  let g3 := Bool.xor x0 x2
  let g4 := Bool.xor g2 g3
  Bool.xor x1 g4

/-- Eight-gate full-binary-basis circuit discovered by falsification search. -/
private def h5 (x0 x1 x2 x3 x4 : Bool) : Bool :=
  let g0 := xnor x1 x3
  let g1 := x2 || x3
  let g2 := xnor x2 g0
  let g3 := Bool.xor x0 g2
  let g4 := lt x0 g0
  let g5 := g1 || (!g4)
  let g6 := lt x4 g5
  Bool.xor g3 g6

/-- Exact truth-table verification of the six-gate four-variable circuit. -/
theorem h4_positiveEven
    (x0 x1 x2 x3 : Bool) :
    h4 x0 x1 x2 x3 = positiveEven4 x0 x1 x2 x3 := by
  cases x0 <;> cases x1 <;> cases x2 <;> cases x3 <;> decide

/-- Exact truth-table verification of the eight-gate five-variable circuit. -/
theorem h5_positiveEven
    (x0 x1 x2 x3 x4 : Bool) :
    h5 x0 x1 x2 x3 x4 = positiveEven5 x0 x1 x2 x3 x4 := by
  cases x0 <;> cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> decide

#print axioms positiveEven_agrees_on_four_shells
#print axioms positiveEven_gate_budget
#print axioms h4_positiveEven
#print axioms h5_positiveEven

end PNPExactLayerLocalCompletionFinite
