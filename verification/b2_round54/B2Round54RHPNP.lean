import Mathlib
import B2Round56Core

namespace B2Round54

def rhDiagonalSpike (M l : Nat) : Nat := if M = l then 1 else 0

theorem rh_pointwise_tail_does_not_imply_cofinal_tail :
    And
      (forall l : Nat, exists N : Nat, forall M : Nat,
        N <= M -> rhDiagonalSpike M l = 0)
      (forall M : Nat, rhDiagonalSpike M M = 1) := by
  constructor
  · intro l
    refine ⟨l + 1, ?_⟩
    intro M hM
    unfold rhDiagonalSpike
    split
    · rename_i hEq
      omega
    · rfl
  · intro M
    simp [rhDiagonalSpike]

theorem pnp_shared_prefix_congestion_has_no_fixed_factor
    (C : Int) (hC : 0 <= C) :
    exists k : Int, And (0 < k) (C * (2 * k - 1) < k * k) := by
  refine ⟨2 * C + 2, by linarith, ?_⟩
  nlinarith [sq_nonneg C]

#print axioms rh_pointwise_tail_does_not_imply_cofinal_tail
#print axioms pnp_shared_prefix_congestion_has_no_fixed_factor

end B2Round54
