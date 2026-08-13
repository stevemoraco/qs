import Std.Tactic.Omega

namespace RHLogHardyRenormalizedCorrelation

def Ledger (energy diagonal cross : Int) : Prop :=
  energy = diagonal + cross

def Within (value center budget : Int) : Prop :=
  center - budget ≤ value ∧ value ≤ center + budget

theorem energy_upper_of_renormalized_cross_upper
    (energy diagonal cross renormalizer budget target : Int)
    (hledger : Ledger energy diagonal cross)
    (hdiag : Within diagonal renormalizer budget)
    (hcross : cross + renormalizer ≤ target) :
    energy ≤ target + budget := by
  unfold Ledger at hledger
  unfold Within at hdiag
  omega

theorem renormalized_cross_upper_of_energy_upper
    (energy diagonal cross renormalizer budget target : Int)
    (hledger : Ledger energy diagonal cross)
    (hdiag : Within diagonal renormalizer budget)
    (henergy : energy ≤ target) :
    cross + renormalizer ≤ target + budget := by
  unfold Ledger at hledger
  unfold Within at hdiag
  omega

theorem renormalized_cross_lower_of_nonnegative_energy
    (energy diagonal cross renormalizer budget : Int)
    (hledger : Ledger energy diagonal cross)
    (hdiag : Within diagonal renormalizer budget)
    (henergy : 0 ≤ energy) :
    -budget ≤ cross + renormalizer := by
  unfold Ledger at hledger
  unfold Within at hdiag
  omega

theorem exact_energy_target_from_cross_margin
    (energy diagonal cross renormalizer budget target : Int)
    (hledger : Ledger energy diagonal cross)
    (hdiag : Within diagonal renormalizer budget)
    (hcross : cross + renormalizer ≤ target - budget) :
    energy ≤ target := by
  unfold Ledger at hledger
  unfold Within at hdiag
  omega

def twoPointDiagonal (x y : Int) : Int := x * x + y * y

def twoPointCross (x y : Int) : Int := -2 * x * y

def twoPointEnergy (x y : Int) : Int := (x - y) * (x - y)

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
