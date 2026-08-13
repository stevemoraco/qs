import Init.Data.Int.Order

namespace RHLogHardyRenormalizedCorrelation

/-- A finite energy ledger splits a physical total into diagonal and signed cross terms. -/
def Ledger (energy diagonal cross : Int) : Prop :=
  energy = diagonal + cross

/-- `value` lies within additive `budget` of `center`. -/
def Within (value center budget : Int) : Prop :=
  center ≤ value + budget ∧ value ≤ center + budget

/--
If the diagonal differs from its explicit renormalizer by at most `budget`,
an upper bound for the renormalized cross term gives an upper bound for the
physical energy with exactly that additive defect.
-/
theorem energy_upper_of_renormalized_cross_upper
    (energy diagonal cross renormalizer budget target : Int)
    (hledger : Ledger energy diagonal cross)
    (hdiag : Within diagonal renormalizer budget)
    (hcross : cross + renormalizer ≤ target) :
    energy ≤ target + budget := by
  calc
    energy = diagonal + cross := hledger
    _ ≤ (renormalizer + budget) + cross := Int.add_le_add_right hdiag.2 cross
    _ = (cross + renormalizer) + budget := by
      simp [Int.add_assoc, Int.add_comm, Int.add_left_comm]
    _ ≤ target + budget := Int.add_le_add_right hcross budget

/--
Conversely, an upper bound for the physical energy controls the renormalized
cross term, again losing only the explicit diagonal defect.
-/
theorem renormalized_cross_upper_of_energy_upper
    (energy diagonal cross renormalizer budget target : Int)
    (hledger : Ledger energy diagonal cross)
    (hdiag : Within diagonal renormalizer budget)
    (henergy : energy ≤ target) :
    cross + renormalizer ≤ target + budget := by
  calc
    cross + renormalizer ≤ cross + (diagonal + budget) :=
      Int.add_le_add_left hdiag.1 cross
    _ = (diagonal + cross) + budget := by
      simp [Int.add_assoc, Int.add_comm, Int.add_left_comm]
    _ = energy + budget := by rw [← hledger]
    _ ≤ target + budget := Int.add_le_add_right henergy budget

/--
Nonnegativity of the physical energy supplies the missing lower bound for the
renormalized cross term. Thus only an upper bound is a live analytic debt once
the diagonal asymptotic has a uniform error budget.
-/
theorem renormalized_cross_lower_of_nonnegative_energy
    (energy diagonal cross renormalizer budget : Int)
    (hledger : Ledger energy diagonal cross)
    (hdiag : Within diagonal renormalizer budget)
    (henergy : 0 ≤ energy) :
    0 ≤ cross + renormalizer + budget := by
  calc
    0 ≤ energy := henergy
    _ = diagonal + cross := hledger
    _ ≤ (renormalizer + budget) + cross := Int.add_le_add_right hdiag.2 cross
    _ = cross + renormalizer + budget := by
      simp [Int.add_assoc, Int.add_comm, Int.add_left_comm]

/--
A full `budget` of margin in the renormalized cross estimate pays the complete
diagonal realization defect and returns the desired terminal energy bound.
-/
theorem exact_energy_target_from_cross_margin
    (energy diagonal cross renormalizer budget target : Int)
    (hledger : Ledger energy diagonal cross)
    (hdiag : Within diagonal renormalizer budget)
    (hcross : cross + renormalizer + budget ≤ target) :
    energy ≤ target := by
  calc
    energy = diagonal + cross := hledger
    _ ≤ (renormalizer + budget) + cross := Int.add_le_add_right hdiag.2 cross
    _ = cross + renormalizer + budget := by
      simp [Int.add_assoc, Int.add_comm, Int.add_left_comm]
    _ ≤ target := hcross

/-- The diagonal part of the smallest two-coordinate quadratic model. -/
def twoPointDiagonal (x y : Int) : Int :=
  x * x + y * y

/-- The ordered signed cross term in the same model. -/
def twoPointCross (x y : Int) : Int :=
  -2 * x * y

/-- The physical square energy in the same model. -/
def twoPointEnergy (x y : Int) : Int :=
  (x - y) * (x - y)

/--
The aligned and anti-aligned witnesses have exactly the same diagonal mass,
but their cross terms and physical energies are different. Marginal/diagonal
control alone therefore cannot certify a cancellation-sensitive energy.
-/
theorem same_diagonal_different_cross_and_energy :
    twoPointDiagonal 1 1 = twoPointDiagonal 1 (-1) ∧
    twoPointCross 1 1 = -2 ∧
    twoPointCross 1 (-1) = 2 ∧
    twoPointEnergy 1 1 = 0 ∧
    twoPointEnergy 1 (-1) = 4 ∧
    Ledger 0 2 (-2) ∧
    Ledger 4 2 2 := by
  decide

#print axioms energy_upper_of_renormalized_cross_upper
#print axioms renormalized_cross_upper_of_energy_upper
#print axioms renormalized_cross_lower_of_nonnegative_energy
#print axioms exact_energy_target_from_cross_margin
#print axioms same_diagonal_different_cross_and_energy

end RHLogHardyRenormalizedCorrelation
