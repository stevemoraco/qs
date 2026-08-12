import Mathlib

namespace MillenniumBraid
namespace PNPPairRestrictionSemanticTightness

def outer (c d a p : Bool) : Bool :=
  if a then c && d
  else if p then (!c) && (!d)
  else Bool.xor c d

def outerCircuit (c d a p : Bool) : Bool :=
  let u := Bool.xor c d
  let v := !(c || d)
  let s := u && (!p)
  let t := v && p
  let w := s || t
  let q := c && d
  let r := w && (!a)
  let z := q && a
  r || z

theorem outerCircuit_correct (c d a p : Bool) :
    outerCircuit c d a p = outer c d a p := by
  cases c <;> cases d <;> cases a <;> cases p <;> decide

theorem dataPairXorContext (x y : Bool) :
    outer false false false (Bool.xor x y) = Bool.xor x y := by
  cases x <;> cases y <;> decide

theorem dataPairAndContext (x y : Bool) :
    outer true true (x && y) (Bool.xor x y) = (x && y) := by
  cases x <;> cases y <;> decide

theorem firstControlDataXorContext (c x : Bool) :
    outer c false false x = Bool.xor c x := by
  cases c <;> cases x <;> decide

theorem firstControlDataAndContext (c x : Bool) :
    outer c true x (!x) = (c && x) := by
  cases c <;> cases x <;> decide

theorem secondControlDataXorContext (d x : Bool) :
    outer false d false x = Bool.xor d x := by
  cases d <;> cases x <;> decide

theorem secondControlDataAndContext (d x : Bool) :
    outer true d x (!x) = (d && x) := by
  cases d <;> cases x <;> decide

theorem controlPairXorContext (c d : Bool) :
    outer c d false false = Bool.xor c d := by
  cases c <;> cases d <;> decide

theorem controlPairAndContext (c d : Bool) :
    outer c d true false = (c && d) := by
  cases c <;> cases d <;> decide

def gateCount (m : ℕ) : ℕ :=
  (m - 1) + (m - 1) + 9

theorem gateCount_eq_two_n_plus_three
    (m : ℕ) (hm : 1 ≤ m) :
    gateCount m = 2 * (m + 2) + 3 := by
  unfold gateCount
  omega

theorem semanticSurplus_eq_five
    (m : ℕ) (hm : 1 ≤ m) :
    gateCount m - (2 * (m + 2) - 2) = 5 := by
  unfold gateCount
  omega

#print axioms outerCircuit_correct
#print axioms dataPairXorContext
#print axioms dataPairAndContext
#print axioms firstControlDataXorContext
#print axioms firstControlDataAndContext
#print axioms secondControlDataXorContext
#print axioms secondControlDataAndContext
#print axioms controlPairXorContext
#print axioms controlPairAndContext
#print axioms gateCount_eq_two_n_plus_three
#print axioms semanticSurplus_eq_five

end PNPPairRestrictionSemanticTightness
end MillenniumBraid
