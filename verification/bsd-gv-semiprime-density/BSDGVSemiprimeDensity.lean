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

def residuePairCount : Nat := Fintype.card ResiduePair

def rowStateCount (p : OddResidue) : Nat :=
  ((Finset.univ : Finset (OddResidue × LegendreSign)).filter
    fun x => accepts p x.1 x.2 = true).card

def acceptedSignCount (s : LegendreSign) : Nat :=
  ((Finset.univ : Finset ResiduePair).filter
    fun x => accepts x.1 x.2 s = true).card

def bothSignPairs : Finset ResiduePair :=
  (Finset.univ : Finset ResiduePair).filter fun x =>
    accepts x.1 x.2 .pos = true ∧
    accepts x.1 x.2 .neg = true

def bothSignPairCount : Nat := bothSignPairs.card

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

/-- There are `8*8=64` ordered odd residue pairs modulo 16. -/
theorem residuePairCount_eq : residuePairCount = 64 := by
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

/-- A residue pair works independently of the Legendre symbol exactly for the
two both-sign pairs. -/
theorem residue_only_pair_iff (p q : OddResidue) :
    (∀ s : LegendreSign, accepts p q s = true) ↔
      ((p = .r3 ∧ q = .r11) ∨ (p = .r11 ∧ q = .r3)) := by
  constructor
  · intro hall
    exact (both_sign_pairs_classification p q).1 ⟨hall .pos, hall .neg⟩
  · intro hpq s
    rcases hpq with hpq | hpq
    · rcases hpq with ⟨rfl, rfl⟩
      cases s <;> decide
    · rcases hpq with ⟨rfl, rfl⟩
      cases s <;> decide

/-- Any selector depending only on the two residues and guaranteed to work for
both Legendre signs contains at most two residue pairs. -/
theorem residue_only_selector_card_le_two
    (S : Finset ResiduePair)
    (h : ∀ x ∈ S, ∀ s : LegendreSign, accepts x.1 x.2 s = true) :
    S.card ≤ 2 := by
  have hsub : S ⊆ bothSignPairs := by
    intro x hx
    simp only [bothSignPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h x hx .pos, h x hx .neg⟩
  calc
    S.card ≤ bothSignPairs.card := Finset.card_le_card hsub
    _ = bothSignPairCount := rfl
    _ = 2 := bothSignPairCount_eq

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

/-- The optimal residue-only core has density coefficient `2/64=1/32`. -/
theorem residue_only_core_fraction_certificate :
    bothSignPairCount * 32 = residuePairCount := by
  decide

/-- The full accepted state count is the four states from the two both-sign
pairs plus twenty-four genuinely sign-sensitive states. -/
theorem character_sensitive_state_decomposition :
    acceptedStateCount = 2 * bothSignPairCount + 24 := by
  decide

/-- The character-sensitive increment has coefficient `24/128=3/16`. -/
theorem character_sensitive_increment_fraction_certificate :
    (acceptedStateCount - 2 * bothSignPairCount) * 16 =
      3 * totalStateCount := by
  decide

#print axioms totalStateCount_eq
#print axioms residuePairCount_eq
#print axioms acceptedStateCount_eq
#print axioms rowStateCount_eq
#print axioms acceptedPosCount_eq
#print axioms acceptedNegCount_eq
#print axioms bothSignPairCount_eq
#print axioms both_sign_pairs_classification
#print axioms residue_only_pair_iff
#print axioms residue_only_selector_card_le_two
#print axioms three_eleven_all_signs
#print axioms eleven_three_all_signs
#print axioms accepts_swap_with_reciprocity
#print axioms ordered_density_fraction_certificate
#print axioms unordered_coefficient_fraction_certificate
#print axioms positive_sign_fraction_certificate
#print axioms negative_sign_fraction_certificate
#print axioms residue_only_core_fraction_certificate
#print axioms character_sensitive_state_decomposition
#print axioms character_sensitive_increment_fraction_certificate

end BSDGVSemiprimeDensity
