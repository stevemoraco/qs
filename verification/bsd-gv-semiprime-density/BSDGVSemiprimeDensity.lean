import Mathlib

/-!
# Finite residue-state core for the Ghosh--Voutier semiprime BSD family

This file verifies only the finite congruence and sign enumeration behind the
global density calculation. It does not formalize primality, quadratic
reciprocity as a theorem about primes, a quadratic large sieve, the prime
number theorem in arithmetic progressions, Selmer groups, or BSD.

The four predicates below are literal residue-class translations of
Ghosh--Voutier's four rank-zero/trivial-2-primary-Sha cases for
`y^2 = x^3 - p q x`.
-/

namespace BSDGVSemiprimeDensity

set_option maxRecDepth 100000

inductive OddResidue where
  | r1 | r3 | r5 | r7 | r9 | r11 | r13 | r15
  deriving DecidableEq, Repr, Fintype

inductive LegendreSign where
  | pos | neg
  deriving DecidableEq, Repr, Fintype

def OddResidue.value : OddResidue → Nat
  | .r1 => 1
  | .r3 => 3
  | .r5 => 5
  | .r7 => 7
  | .r9 => 9
  | .r11 => 11
  | .r13 => 13
  | .r15 => 15

def LegendreSign.isPos : LegendreSign → Bool
  | .pos => true
  | .neg => false

def LegendreSign.isNeg : LegendreSign → Bool
  | .pos => false
  | .neg => true

def diffMod16 (a b : Nat) : Nat := (a + 16 - b) % 16

def isEightOrTwelve (n : Nat) : Bool := (n == 8) || (n == 12)

def gvCaseI (p q : OddResidue) (s : LegendreSign) : Bool :=
  let a := p.value
  let b := q.value
  (a % 4 == 1) &&
  (b % 4 == 1) &&
  (a * b % 16 == 13) &&
  s.isNeg

def gvCaseII (p q : OddResidue) (s : LegendreSign) : Bool :=
  let a := p.value
  let b := q.value
  (!(a % 4 == b % 4)) &&
  (a * b % 8 == 3) &&
  s.isNeg

def gvCaseIII (p q : OddResidue) (s : LegendreSign) : Bool :=
  let a := p.value
  let b := q.value
  (a % 4 == 3) &&
  (b % 4 == 3) &&
  s.isPos &&
  (b % 8 == 3) &&
  isEightOrTwelve (diffMod16 a b)

def gvCaseIV (p q : OddResidue) (s : LegendreSign) : Bool :=
  let a := p.value
  let b := q.value
  (a % 4 == 3) &&
  (b % 4 == 3) &&
  s.isNeg &&
  (a % 8 == 3) &&
  isEightOrTwelve (diffMod16 b a)

def accepts (p q : OddResidue) (s : LegendreSign) : Bool :=
  gvCaseI p q s ||
  gvCaseII p q s ||
  gvCaseIII p q s ||
  gvCaseIV p q s

abbrev State := OddResidue × (OddResidue × LegendreSign)
abbrev ResiduePair := OddResidue × OddResidue

def allStates : Finset State := Finset.univ

def acceptedStateCount : Nat :=
  (allStates.filter fun x => accepts x.1 x.2.1 x.2.2 = true).card

def totalStateCount : Nat := Fintype.card State

def rowStateCount (p : OddResidue) : Nat :=
  ((Finset.univ : Finset (OddResidue × LegendreSign)).filter
    fun x => accepts p x.1 x.2 = true).card

def acceptedSignCount (s : LegendreSign) : Nat :=
  ((Finset.univ : Finset ResiduePair).filter
    fun x => accepts x.1 x.2 s = true).card

def bothSignPairCount : Nat :=
  ((Finset.univ : Finset ResiduePair).filter
    fun x =>
      accepts x.1 x.2 .pos = true &&
      accepts x.1 x.2 .neg = true).card

def expectedRowStateCount : OddResidue → Nat
  | .r3 => 5
  | .r11 => 5
  | _ => 3

def flipSign : LegendreSign → LegendreSign
  | .pos => .neg
  | .neg => .pos

def bothThreeModFour (p q : OddResidue) : Bool :=
  (p.value % 4 == 3) && (q.value % 4 == 3)

def reciprocityTransport
    (p q : OddResidue) (s : LegendreSign) : LegendreSign :=
  match bothThreeModFour p q with
  | true => flipSign s
  | false => s

/-- There are eight odd residue classes, eight choices for the second prime,
and two Legendre signs. -/
theorem totalStateCount_eq : totalStateCount = 128 := by
  decide

/-- Exactly 28 of the 128 residue/sign states satisfy the four conditions. -/
theorem acceptedStateCount_eq : acceptedStateCount = 28 := by
  decide

/-- Fixed-first-residue state counts: five for residues 3 and 11, three
for each of the other six odd residues. -/
theorem rowStateCount_eq (p : OddResidue) :
    rowStateCount p = expectedRowStateCount p := by
  cases p <;> decide

/-- Exactly four accepted states have positive Legendre sign. -/
theorem acceptedPosCount_eq : acceptedSignCount .pos = 4 := by
  decide

/-- Exactly twenty-four accepted states have negative Legendre sign. -/
theorem acceptedNegCount_eq : acceptedSignCount .neg = 24 := by
  decide

/-- Exactly two ordered residue pairs accept both Legendre signs. -/
theorem bothSignPairCount_eq : bothSignPairCount = 2 := by
  decide

/-- The ordered residue pairs accepting both signs are exactly `(3,11)` and
`(11,3)`. -/
theorem both_sign_pairs_classification (p q : OddResidue) :
    (accepts p q .pos = true ∧ accepts p q .neg = true) ↔
      ((p = .r3 ∧ q = .r11) ∨ (p = .r11 ∧ q = .r3)) := by
  cases p <;> cases q <;> decide

/-- The residue pair `(3,11)` works for either Legendre sign. -/
theorem three_eleven_all_signs (s : LegendreSign) :
    accepts .r3 .r11 s = true := by
  cases s <;> decide

/-- The symmetric residue pair `(11,3)` also works for either transported
Legendre sign. -/
theorem eleven_three_all_signs (s : LegendreSign) :
    accepts .r11 .r3 s = true := by
  cases s <;> decide

/-- Swapping the two prime variables preserves the classification after the
finite residue-level sign change dictated by quadratic reciprocity. -/
theorem accepts_swap_with_reciprocity
    (p q : OddResidue) (s : LegendreSign) :
    accepts p q s = accepts q p (reciprocityTransport p q s) := by
  cases p <;> cases q <;> cases s <;> decide

/-- Cross-multiplication certificate for `28/128 = 7/32`. -/
theorem ordered_density_fraction_certificate :
    acceptedStateCount * 32 = 7 * totalStateCount := by
  decide

/-- Cross-multiplication certificate for the unordered-pair main coefficient
`(28/128)/2 = 7/64`. -/
theorem unordered_coefficient_fraction_certificate :
    acceptedStateCount * 64 = 7 * (2 * totalStateCount) := by
  decide

/-- Cross-multiplication certificate for the positive-sign coefficient
`4/128 = 1/32`. -/
theorem positive_sign_fraction_certificate :
    acceptedSignCount .pos * 32 = totalStateCount := by
  decide

/-- Cross-multiplication certificate for the negative-sign coefficient
`24/128 = 3/16`. -/
theorem negative_sign_fraction_certificate :
    acceptedSignCount .neg * 16 = 3 * totalStateCount := by
  decide

#print axioms totalStateCount_eq
#print axioms acceptedStateCount_eq
#print axioms rowStateCount_eq
#print axioms acceptedPosCount_eq
#print axioms acceptedNegCount_eq
#print axioms bothSignPairCount_eq
#print axioms both_sign_pairs_classification
#print axioms three_eleven_all_signs
#print axioms eleven_three_all_signs
#print axioms accepts_swap_with_reciprocity
#print axioms ordered_density_fraction_certificate
#print axioms unordered_coefficient_fraction_certificate
#print axioms positive_sign_fraction_certificate
#print axioms negative_sign_fraction_certificate

end BSDGVSemiprimeDensity
