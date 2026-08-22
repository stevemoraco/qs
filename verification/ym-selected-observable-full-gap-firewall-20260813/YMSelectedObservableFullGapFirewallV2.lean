import Mathlib

namespace Millennium.YangMills.SelectedObservableFullGapFirewall

structure V where
  x0 : Rat
  x1 : Rat
  x2 : Rat
  deriving DecidableEq

def dot (x y : V) : Rat :=
  x.x0 * y.x0 + x.x1 * y.x1 + x.x2 * y.x2

def zeroV : V := { x0 := 0, x1 := 0, x2 := 0 }
def vacuum : V := { x0 := 1, x1 := 0, x2 := 0 }
def hidden : V := { x0 := 0, x1 := 1, x2 := 0 }
def visible : V := { x0 := 0, x1 := 0, x2 := 1 }

def transfer (n : Nat) (x : V) : V :=
  { x0 := x.x0
    x1 := x.x1
    x2 := (1 / 2 : Rat) ^ n * x.x2 }

theorem visible_correlation (n : Nat) :
    dot visible (transfer n visible) = (1 / 2 : Rat) ^ n := by
  simp [dot, visible, transfer]

theorem visible_nonzero : Not (visible = zeroV) := by
  norm_num [visible, zeroV]

theorem visible_centered : dot vacuum visible = 0 := by
  norm_num [dot, vacuum, visible]

theorem hidden_nonzero : Not (hidden = zeroV) := by
  norm_num [hidden, zeroV]

theorem hidden_centered : dot vacuum hidden = 0 := by
  norm_num [dot, vacuum, hidden]

theorem hidden_invisible : dot visible hidden = 0 := by
  norm_num [dot, visible, hidden]

theorem hidden_fixed (n : Nat) : transfer n hidden = hidden := by
  ext <;> simp [transfer, hidden]

theorem selected_decay_does_not_force_full_transfer_gap :
    And
      (forall n : Nat,
        dot visible (transfer n visible) = (1 / 2 : Rat) ^ n)
      (And
        (Not (visible = zeroV))
        (And
          (dot vacuum visible = 0)
          (Exists fun h : V =>
            And
              (Not (h = zeroV))
              (And
                (dot vacuum h = 0)
                (And
                  (dot visible h = 0)
                  (forall n : Nat, transfer n h = h)))))) := by
  refine And.intro visible_correlation ?_
  refine And.intro visible_nonzero ?_
  refine And.intro visible_centered ?_
  refine Exists.intro hidden ?_
  refine And.intro hidden_nonzero ?_
  refine And.intro hidden_centered ?_
  refine And.intro hidden_invisible hidden_fixed

#print axioms visible_correlation
#print axioms visible_nonzero
#print axioms visible_centered
#print axioms hidden_nonzero
#print axioms hidden_centered
#print axioms hidden_invisible
#print axioms hidden_fixed
#print axioms selected_decay_does_not_force_full_transfer_gap

end Millennium.YangMills.SelectedObservableFullGapFirewall
