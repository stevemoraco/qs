import BSDGVDiscriminantHeight

/-!
# Positive-root-number spectrum for the BSD semiprime family

This module certifies the finite residue-state consequences of the external
corrected `j=1728` root-number formula. For odd squarefree `D`, that formula
specializes to

`W(y^2 = x^3 - D*x) = +1` exactly for
`D = 1, 3, 11, 13 (mod 16)`.

The local root-number theorem itself is not formalized here.
-/

namespace BSDGVSemiprimeDensity

set_option maxRecDepth 100000

/-- Product residue of the two odd prime classes modulo 16. -/
def productResidue (p q : OddResidue) : Nat :=
  (p.value * q.value) % 16

/-- Finite shell of the corrected squarefree `j=1728` root-number formula. -/
def rootNumberPositive (p q : OddResidue) : Bool :=
  let d := productResidue p q
  (d == 1) || (d == 3) || (d == 11) || (d == 13)

def rootPositiveStates : Finset State :=
  allStates.filter fun x => rootNumberPositive x.1 x.2.1 = true

def rootPositiveStateCount : Nat := rootPositiveStates.card

/-- Exactly half of the 128 residue/Legendre states have positive global root
number in the odd squarefree quartic-twist family. -/
theorem rootPositiveStateCount_eq : rootPositiveStateCount = 64 := by
  decide

/-- Every Ghosh--Voutier accepted state lies in the positive-root-number
sector. -/
theorem accepted_implies_root_positive
    (p q : OddResidue) (s : LegendreSign) :
    accepts p q s = true → rootNumberPositive p q = true := by
  cases p <;> cases q <;> cases s <;> decide

/-- Finset form of the accepted-to-positive-root-number containment. -/
theorem acceptedStates_subset_rootPositiveStates :
    acceptedStates ⊆ rootPositiveStates := by
  intro x hx
  simp only [acceptedStates, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  simp only [rootPositiveStates, Finset.mem_filter, Finset.mem_univ, true_and]
  exact accepted_implies_root_positive x.1 x.2.1 x.2.2 hx

/-- Cross-multiplication certificate for the relative fraction
`28/64 = 7/16`. -/
theorem positive_root_complete_bsd_fraction_certificate :
    acceptedStateCount * 16 = 7 * rootPositiveStateCount := by
  decide

/-- Half of the total minimal-discriminant coefficient `3/4` is `3/8`. -/
theorem positive_root_discriminant_family_coefficient :
    (1 / 2 : ℚ) * (3 / 4) = 3 / 8 := by
  norm_num

/-- The certified minimal-discriminant coefficient has relative density
`7/16` inside the positive-root-number family. -/
theorem positive_root_discriminant_relative_density :
    (21 / 128 : ℚ) / (3 / 8) = 7 / 16 := by
  norm_num

#print axioms rootPositiveStateCount_eq
#print axioms accepted_implies_root_positive
#print axioms acceptedStates_subset_rootPositiveStates
#print axioms positive_root_complete_bsd_fraction_certificate
#print axioms positive_root_discriminant_family_coefficient
#print axioms positive_root_discriminant_relative_density

end BSDGVSemiprimeDensity
