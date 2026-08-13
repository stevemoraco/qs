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

/-- Number of all residue/sign states having one fixed product residue. -/
def productResidueStateCount (r : OddResidue) : Nat :=
  (allStates.filter fun x => productResidue x.1 x.2.1 = r.value).card

/-- Number of accepted states having one fixed product residue. -/
def acceptedProductResidueStateCount (r : OddResidue) : Nat :=
  (acceptedStates.filter fun x => productResidue x.1 x.2.1 = r.value).card

/-- Exact accepted-state spectrum by product residue. -/
def expectedAcceptedProductResidueStateCount : OddResidue → Nat
  | .r1 => 4
  | .r3 => 8
  | .r5 => 0
  | .r7 => 0
  | .r9 => 0
  | .r11 => 8
  | .r13 => 8
  | .r15 => 0

/-- Exactly half of the 128 residue/Legendre states have positive global root
number in the odd squarefree quartic-twist family. -/
theorem rootPositiveStateCount_eq : rootPositiveStateCount = 64 := by
  decide

/-- Every product residue contains exactly sixteen residue/sign states. -/
theorem productResidueStateCount_eq (r : OddResidue) :
    productResidueStateCount r = 16 := by
  cases r <;> decide

/-- Exact accepted-state counts by product residue:
`4,8,0,0,0,8,8,0` in the order `1,3,5,7,9,11,13,15`. -/
theorem acceptedProductResidueStateCount_eq (r : OddResidue) :
    acceptedProductResidueStateCount r =
      expectedAcceptedProductResidueStateCount r := by
  cases r <;> decide

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

/-- In product residue `1`, exactly one quarter of the states are certified. -/
theorem residue_one_certified_quarter :
    acceptedProductResidueStateCount .r1 * 4 =
      productResidueStateCount .r1 := by
  decide

/-- In product residue `3`, exactly one half of the states are certified. -/
theorem residue_three_certified_half :
    acceptedProductResidueStateCount .r3 * 2 =
      productResidueStateCount .r3 := by
  decide

/-- In product residue `11`, exactly one half of the states are certified. -/
theorem residue_eleven_certified_half :
    acceptedProductResidueStateCount .r11 * 2 =
      productResidueStateCount .r11 := by
  decide

/-- In product residue `13`, exactly one half of the states are certified. -/
theorem residue_thirteen_certified_half :
    acceptedProductResidueStateCount .r13 * 2 =
      productResidueStateCount .r13 := by
  decide

/-- Every negative-root-number residue class contains zero accepted states. -/
theorem negative_root_residue_classes_unaccepted :
    acceptedProductResidueStateCount .r5 = 0 ∧
    acceptedProductResidueStateCount .r7 = 0 ∧
    acceptedProductResidueStateCount .r9 = 0 ∧
    acceptedProductResidueStateCount .r15 = 0 := by
  decide

/-- Cross-multiplication certificate for the relative fraction
`28/64 = 7/16`. -/
theorem positive_root_complete_bsd_fraction_certificate :
    acceptedStateCount * 16 = 7 * rootPositiveStateCount := by
  decide

/-- A selector using only the two residue classes and valid for both Legendre
signs reaches at most the two both-sign pairs. Their four sign states form
exactly `1/16` of the positive-root-number state space. -/
theorem residue_only_positive_root_fraction_certificate :
    (2 * bothSignPairCount) * 16 = rootPositiveStateCount := by
  decide

/-- Retaining one Legendre-symbol bit enlarges the certified state set by the
exact factor seven. -/
theorem character_bit_sevenfold_gain :
    acceptedStateCount = 7 * (2 * bothSignPairCount) := by
  decide

/-- The genuinely character-sensitive increment is `24/64 = 3/8` of the
positive-root-number state space. -/
theorem character_sensitive_positive_root_fraction_certificate :
    (acceptedStateCount - 2 * bothSignPairCount) * 8 =
      3 * rootPositiveStateCount := by
  decide

/-- Six sevenths of the certified family comes from states that cannot be
recovered by a residue-only selector. -/
theorem character_sensitive_certified_share :
    (24 / 28 : ℚ) = 6 / 7 := by
  norm_num

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
#print axioms productResidueStateCount_eq
#print axioms acceptedProductResidueStateCount_eq
#print axioms accepted_implies_root_positive
#print axioms acceptedStates_subset_rootPositiveStates
#print axioms residue_one_certified_quarter
#print axioms residue_three_certified_half
#print axioms residue_eleven_certified_half
#print axioms residue_thirteen_certified_half
#print axioms negative_root_residue_classes_unaccepted
#print axioms positive_root_complete_bsd_fraction_certificate
#print axioms residue_only_positive_root_fraction_certificate
#print axioms character_bit_sevenfold_gain
#print axioms character_sensitive_positive_root_fraction_certificate
#print axioms character_sensitive_certified_share
#print axioms positive_root_discriminant_family_coefficient
#print axioms positive_root_discriminant_relative_density

end BSDGVSemiprimeDensity
