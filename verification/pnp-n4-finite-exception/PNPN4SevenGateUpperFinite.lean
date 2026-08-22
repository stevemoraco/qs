import Mathlib

/-!
# Four-variable two-sided obstruction: explicit seven-gate upper witness

HONESTY
* This file formalizes only evaluation of the explicit seven-gate circuit,
  its scalar gate/slack count, and the finite single-owner counting failure.
* It does NOT formalize the exhaustive six-gate lower search, Boolean-circuit
  minimality, critical paths, Chen--Li--Yang magnification, or P versus NP.
* No `sorry`, `admit`, or project axiom occurs.
-/

namespace Millennium
namespace PVsNP
namespace N4SevenGate

/-- Truth table `0001`: NOR under input index `(a,b)`. -/
def gate1 (a b : Bool) : Bool := !(a || b)

/-- Truth table `0110`: XOR. -/
def gate6 (a b : Bool) : Bool := (a && !b) || (!a && b)

/-- Truth table `1110`: OR. -/
def gateE (a b : Bool) : Bool := a || b

/-- Truth table `1001`: XNOR. -/
def gate9 (a b : Bool) : Bool := !(gate6 a b)

/-- The seven-gate witness returned by the exhaustive audit. -/
def circuit (x0 x1 x2 x3 : Bool) : Bool :=
  gate9
    (gateE (gate1 x0 x3) (gate1 x1 x2))
    (gateE (gate6 x1 x2) (gate6 x0 x3))

def bitNat (x : Bool) : Nat := if x then 1 else 0

def hammingWeight (x0 x1 x2 x3 : Bool) : Nat :=
  bitNat x0 + bitNat x1 + bitNat x2 + bitNat x3

/-- The length-four sparse-language slice: positive exactly at weights 1 and 4. -/
def target (x0 x1 x2 x3 : Bool) : Bool :=
  decide
    (hammingWeight x0 x1 x2 x3 = 1 ∨
     hammingWeight x0 x1 x2 x3 = 4)

/-- Exhaustive evaluation of all sixteen assignments. -/
theorem circuit_correct :
    ∀ x0 x1 x2 x3 : Bool,
      circuit x0 x1 x2 x3 = target x0 x1 x2 x3 := by
  native_decide

/-- Seven gates are exactly one above the `2n-2` baseline at `n=4`. -/
theorem gate_count_is_baseline_plus_one :
    (7 : Nat) = 2 * 4 - 2 + 1 := by
  omega

/-- Four length-two cyclic windows cannot be charged to one single-owner unit
with congestion two. -/
theorem single_owner_window_charge_impossible :
    ¬ (4 : Nat) ≤ 2 * 1 := by
  omega

/-- A two-owner repair has exactly enough finite capacity. -/
theorem two_owner_window_capacity_exact :
    (4 : Nat) = 2 * 2 * 1 := by
  omega

#print axioms circuit_correct
#print axioms gate_count_is_baseline_plus_one
#print axioms single_owner_window_charge_impossible
#print axioms two_owner_window_capacity_exact

end N4SevenGate
end PVsNP
end Millennium
