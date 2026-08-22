import Init.Data.Nat.MinMax

namespace RHLogHardyEndpointQuantifierCore

/--
`Vanishes a` is the exact tail-uniform quantifier used by the finite
shadow of the endpoint Abel argument.
-/
def Vanishes (a : Nat → Nat) : Prop :=
  ∀ ε : Nat, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → a n < ε

/--
`EventuallyAtLeast a r` records a fixed terminal floor.
In the analytic application, a nonzero boundary residue supplies such a
floor for a discretized modulus after the radial parameter is small enough.
-/
def EventuallyAtLeast (a : Nat → Nat) (r : Nat) : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n → r ≤ a n

/--
A tail-uniformly vanishing sequence cannot retain a positive terminal floor.
This is only finite quantifier/order logic; no Mellin transform or zeta
function is represented here.
-/
theorem vanishing_excludes_positive_floor
    (a : Nat → Nat)
    (r : Nat)
    (hVanishes : Vanishes a)
    (hPositive : 0 < r)
    (hFloor : EventuallyAtLeast a r) :
    False := by
  obtain ⟨Nv, hNv⟩ := hVanishes r hPositive
  obtain ⟨Nf, hNf⟩ := hFloor
  let n := Nat.max Nv Nf
  have hNvLe : Nv ≤ n := by
    exact Nat.le_max_left Nv Nf
  have hNfLe : Nf ≤ n := by
    exact Nat.le_max_right Nv Nf
  have hSmall : a n < r := hNv n hNvLe
  have hLarge : r ≤ a n := hNf n hNfLe
  exact (Nat.lt_irrefl r) (Nat.lt_of_le_of_lt hLarge hSmall)

/--
A fixed positive floor directly refutes tail-uniform vanishing.
-/
theorem positive_floor_forces_not_vanishing
    (a : Nat → Nat)
    (r : Nat)
    (hPositive : 0 < r)
    (hFloor : EventuallyAtLeast a r) :
    ¬ Vanishes a := by
  intro hVanishes
  exact vanishing_excludes_positive_floor a r hVanishes hPositive hFloor

/--
If one scale is no smaller than another, then doubling the smaller scale
has square no larger than the square of the mixed scale. This is the finite
nonnegative arithmetic shadow of the bounded tail factor in the endpoint
Cauchy--Schwarz estimate.
-/
theorem doubled_square_le_mixed_square
    (r d : Nat)
    (h : r ≤ d) :
    (r + r) * (r + r) ≤ (d + r) * (d + r) := by
  have hsum : r + r ≤ d + r := Nat.add_le_add_right h r
  exact Nat.mul_le_mul hsum hsum

/--
Any upper budget available at the mixed scale transfers to the doubled
smaller scale after multiplying by the same nonnegative tail mass.
-/
theorem doubled_tail_budget_transfer
    (r d tail budget : Nat)
    (hScale : r ≤ d)
    (hBudget : (d + r) * (d + r) * tail ≤ budget) :
    (r + r) * (r + r) * tail ≤ budget := by
  have hSquare :
      (r + r) * (r + r) ≤ (d + r) * (d + r) :=
    doubled_square_le_mixed_square r d hScale
  have hWeighted :
      (r + r) * (r + r) * tail ≤ (d + r) * (d + r) * tail :=
    Nat.mul_le_mul hSquare (Nat.le_refl tail)
  exact Nat.le_trans hWeighted hBudget

#print axioms vanishing_excludes_positive_floor
#print axioms positive_floor_forces_not_vanishing
#print axioms doubled_square_le_mixed_square
#print axioms doubled_tail_budget_transfer

end RHLogHardyEndpointQuantifierCore
