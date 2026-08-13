import Mathlib

namespace YMGate

inductive State where
  | vacuum
  | hidden
  | visible
  deriving DecidableEq

def transferEigen (n : Nat) : State -> Rat
  | .vacuum => 1
  | .hidden => 1
  | .visible => (1 / 2 : Rat) ^ n

theorem visible_decay (n : Nat) :
    transferEigen n .visible = (1 / 2 : Rat) ^ n := by
  rfl

theorem hidden_at_vacuum_eigenvalue (n : Nat) :
    transferEigen n .hidden = 1 := by
  rfl

theorem hidden_is_nonvacuum : Not (State.hidden = State.vacuum) := by
  decide

theorem selected_decay_with_hidden_ungapped :
    And
      (forall n : Nat, transferEigen n .visible = (1 / 2 : Rat) ^ n)
      (And
        (Not (State.hidden = State.vacuum))
        (forall n : Nat, transferEigen n .hidden = 1)) := by
  exact And.intro visible_decay (And.intro hidden_is_nonvacuum hidden_at_vacuum_eigenvalue)

#print axioms visible_decay
#print axioms hidden_at_vacuum_eigenvalue
#print axioms hidden_is_nonvacuum
#print axioms selected_decay_with_hidden_ungapped

end YMGate
