import Mathlib

namespace NavierStokesCoveringCountermodel

/-- An equal-mass finite partition can have total mass one while every
single cell has arbitrarily small mass.  This is the finite algebraic
countermodel behind the failure of any pigeonhole lower bound depending
only on overlap and not on cover cardinality.

Interpret `N` pairwise disjoint cells as a cover with overlap exactly one.
Each cell has mass `1/N`; their algebraic total is one. -/
theorem equalCellTotal (N : ℕ) (hN : 0 < N) :
    (N : ℝ) * (1 / (N : ℝ)) = 1 := by
  have hNneNat : N ≠ 0 := Nat.ne_of_gt hN
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hNneNat
  field_simp [hNne]

/-- For every proposed positive scale-uniform fraction `c`, there is a
finite overlap-one equal-cell model of total mass one whose every cell
mass `1/N` is strictly below `c`.

Thus bounded overlap alone cannot imply that one member of an arbitrarily
fine cover carries a fixed positive fraction of the total mass. -/
theorem noUniformSingleCellFraction (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ,
      0 < N ∧
      (N : ℝ) * (1 / (N : ℝ)) = 1 ∧
      1 / (N : ℝ) < c := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / c)
  have hcInv : 0 < (1 / c : ℝ) := one_div_pos.mpr hc
  have hNposR : 0 < (N : ℝ) := lt_trans hcInv hN
  have hNpos : 0 < N := by exact_mod_cast hNposR
  have htotal : (N : ℝ) * (1 / (N : ℝ)) = 1 :=
    equalCellTotal N hNpos
  have hmul : 1 < (N : ℝ) * c := (div_lt_iff₀ hc).mp hN
  have hmul' : 1 < c * (N : ℝ) := by
    simpa [mul_comm] using hmul
  have hsmall : 1 / (N : ℝ) < c :=
    (div_lt_iff₀ hNposR).2 hmul'
  exact ⟨N, hNpos, htotal, hsmall⟩

/-- Abstract ledger model for auditing a later-added output channel.
`typedOutput` represents the channels set to zero by the original typed-zero
definition; `ancestorOutput` represents a new channel added only to the
external ledger used by a later seeding theorem. -/
structure ExtendedLedger where
  typedOutput : ℕ
  ancestorOutput : ℕ
  deriving DecidableEq

/-- The original typed-zero predicate sees only the originally declared
output channels. -/
def typedZero (L : ExtendedLedger) : Prop :=
  L.typedOutput = 0

/-- The later external-zero predicate also includes the ancestor channel. -/
def externalZero (L : ExtendedLedger) : Prop :=
  L.typedOutput + L.ancestorOutput = 0

/-- Finite countermodel to the implication
`typed zero-output -> external ledger zero` when a new nonnegative ancestor
channel is added but is not included in the typed-zero hypothesis. -/
theorem typedZeroDoesNotImplyExternalZero :
    ∃ L : ExtendedLedger, typedZero L ∧ ¬ externalZero L := by
  refine ⟨{ typedOutput := 0, ancestorOutput := 1 }, ?_, ?_⟩
  · rfl
  · norm_num [externalZero]

/-- A two-scale score record.  `largerScore` is the score on the larger
packet and `smallerScore` is the score on a strict descendant. -/
structure TwoScaleScore where
  largerScore : ℕ
  smallerScore : ℕ
  threshold : ℕ
  deriving DecidableEq

/-- The orientation printed in the first-threshold definitions: the larger
packet crosses while every strict descendant lies below threshold. -/
def highLargerLowDescendant (S : TwoScaleScore) : Prop :=
  S.threshold ≤ S.largerScore ∧ S.smallerScore < S.threshold

/-- The opposite orientation used by a later phrase "small parent, first
crossing child". -/
def lowLargerHighDescendant (S : TwoScaleScore) : Prop :=
  S.largerScore < S.threshold ∧ S.threshold ≤ S.smallerScore

/-- The two threshold orientations are not interchangeable by logic alone. -/
theorem firstThresholdOrientationCountermodel :
    ∃ S : TwoScaleScore,
      highLargerLowDescendant S ∧ ¬ lowLargerHighDescendant S := by
  refine ⟨{ largerScore := 2, smallerScore := 0, threshold := 1 }, ?_, ?_⟩
  · norm_num [highLargerLowDescendant]
  · norm_num [lowLargerHighDescendant]

/-- Score and spacetime mass are distinct currencies unless an inequality
relating them is assumed. -/
structure ScoreMassRecord where
  score : ℕ
  spacetimeMass : ℕ
  threshold : ℕ
  deriving DecidableEq

/-- A packet can be numerically subthreshold in score while its spacetime
mass exceeds the same threshold.  Thus score smallness does not by itself
supply the mass seed required by a separate theorem. -/
theorem subthresholdScoreDoesNotImplySmallMass :
    ∃ S : ScoreMassRecord,
      S.score < S.threshold ∧ S.threshold ≤ S.spacetimeMass := by
  exact ⟨{ score := 0, spacetimeMass := 2, threshold := 1 }, by norm_num⟩

#print axioms equalCellTotal
#print axioms noUniformSingleCellFraction
#print axioms typedZeroDoesNotImplyExternalZero
#print axioms firstThresholdOrientationCountermodel
#print axioms subthresholdScoreDoesNotImplySmallMass

end NavierStokesCoveringCountermodel
