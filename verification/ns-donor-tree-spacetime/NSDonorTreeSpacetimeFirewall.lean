import Mathlib

/-!
# Navier--Stokes donor-tree to spacetime firewall

This file contains finite and scalar consequences only.  It separates a mass
ledger on donor labels from support information in a target point space, and
records the elementary obstruction posed by a positive atom to an all-scale
linear growth estimate.
-/

namespace MillenniumBraid
namespace NSDonorTreeSpacetimeFirewall

inductive Point
  | singular
  | regular
  deriving DecidableEq, Fintype

inductive Label
  | donor
  deriving DecidableEq, Fintype

def weight : Label → ℕ
  | .donor => 1

def treeBudget : ℕ := 1

def pushRegular : Label → Point
  | .donor => .regular

def pushSingular : Label → Point
  | .donor => .singular

def labelTotal : ℕ :=
  Finset.univ.sum weight

def massAt (push : Label → Point) (x : Point) : ℕ :=
  Finset.univ.sum (fun label => if push label = x then weight label else 0)

/-- The one-donor ledger saturates its one-unit tree budget. -/
theorem oneDonorCarlesonLedger :
    labelTotal ≤ treeBudget := by
  decide

/-- The label ledger has strictly positive mass. -/
theorem labelTotalPositive :
    0 < labelTotal := by
  decide

/-- Sending the donor to the regular point leaves zero singular mass. -/
theorem regularPushHasNoSingularMass :
    massAt pushRegular .singular = 0 := by
  decide

/-- Sending the same donor to the regular point preserves its full mass there. -/
theorem regularPushHasFullRegularMass :
    massAt pushRegular .regular = 1 := by
  decide

/-- Sending the same donor to the singular point puts its full mass there. -/
theorem singularPushHasFullSingularMass :
    massAt pushSingular .singular = 1 := by
  decide

/-- The same donor mass and tree budget are compatible with opposite support
landing in the target point space. -/
theorem sameLedgerOppositeSingularLanding :
    labelTotal = 1 ∧
      massAt pushRegular .singular = 0 ∧
      massAt pushSingular .singular = 1 := by
  decide

/-- A positive scalar atom always beats a proposed linear Frostman envelope
at some positive scale. -/
theorem positiveAtomViolatesLinearFrostman
    (m C : ℝ) (hm : 0 < m) (hC : 0 ≤ C) :
    ∃ r : ℝ, 0 < r ∧ C * r < m := by
  have hden : 0 < C + 1 := by
    linarith
  refine ⟨m / (C + 1), div_pos hm hden, ?_⟩
  calc
    C * (m / (C + 1)) = (C * m) / (C + 1) := by ring
    _ < m := by
      apply (div_lt_iff₀ hden).2
      nlinarith

/-- Consequently an all-positive-scale linear upper bound cannot coexist with
one positive atom. -/
theorem allScaleLinearBoundKillsPositiveAtom
    (m C : ℝ) (hm : 0 < m) (hC : 0 ≤ C)
    (hbound : ∀ r : ℝ, 0 < r → m ≤ C * r) : False := by
  obtain ⟨r, hr, hstrict⟩ := positiveAtomViolatesLinearFrostman m C hm hC
  exact (not_lt_of_ge (hbound r hr)) hstrict

#print axioms oneDonorCarlesonLedger
#print axioms labelTotalPositive
#print axioms regularPushHasNoSingularMass
#print axioms regularPushHasFullRegularMass
#print axioms singularPushHasFullSingularMass
#print axioms sameLedgerOppositeSingularLanding
#print axioms positiveAtomViolatesLinearFrostman
#print axioms allScaleLinearBoundKillsPositiveAtom

end NSDonorTreeSpacetimeFirewall
end MillenniumBraid
