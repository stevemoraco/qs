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

/-- Three consecutive score levels: a larger ancestor, the packet declared
first-threshold, and one strict descendant of that crossing packet. -/
structure ThreeScaleScore where
  ancestorScore : ℕ
  crossingScore : ℕ
  descendantScore : ℕ
  threshold : ℕ
  deriving DecidableEq

/-- The displayed first-threshold definition controls the crossing packet
and its strict descendants.  It does not mention the larger ancestor. -/
def printedFirstThreshold (S : ThreeScaleScore) : Prop :=
  S.threshold ≤ S.crossingScore ∧ S.descendantScore < S.threshold

/-- The later energy-seeding prose additionally needs a low larger parent
immediately before the crossing packet. -/
def lowAncestorHighCrossing (S : ThreeScaleScore) : Prop :=
  S.ancestorScore < S.threshold ∧ S.threshold ≤ S.crossingScore

/-- The displayed first-threshold condition alone does not imply the
additional low-ancestor premise.  A separate adjacency/continuity theorem
is required to pass from one formulation to the other. -/
theorem firstThresholdDoesNotSupplyLowAncestor :
    ∃ S : ThreeScaleScore,
      printedFirstThreshold S ∧ ¬ lowAncestorHighCrossing S := by
  refine ⟨{
    ancestorScore := 2,
    crossingScore := 2,
    descendantScore := 0,
    threshold := 1
  }, ?_, ?_⟩
  · norm_num [printedFirstThreshold]
  · norm_num [lowAncestorHighCrossing]

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

/-- The atom carrying the whole ledger mass in the finite cross-scale
countermodel. -/
def atomPoint (N : ℕ) : Fin (N + 1) :=
  ⟨N, Nat.lt_succ_self N⟩

/-- One packet at each labelled scale.  As the scale index grows, these
sets are nested decreasing, and every one contains the terminal atom. -/
def packetAtScale (N : ℕ) (k : Fin N) : Set (Fin (N + 1)) :=
  {x | k.val ≤ x.val}

/-- Unit point mass at `atomPoint N`. -/
noncomputable def atomMass (N : ℕ) (A : Set (Fin (N + 1))) : ℕ := by
  classical
  exact if atomPoint N ∈ A then 1 else 0

lemma packetAtScaleContainsAtom (N : ℕ) (k : Fin N) :
    atomPoint N ∈ packetAtScale N k := by
  change k.val ≤ N
  exact Nat.le_of_lt k.isLt

lemma packetAtScaleAntitone (N : ℕ) {i j : Fin N} (hij : i ≤ j) :
    packetAtScale N j ⊆ packetAtScale N i := by
  intro x hx
  change i.val ≤ x.val
  exact le_trans hij hx

lemma everyPacketHasFullAtomMass (N : ℕ) (k : Fin N) :
    atomMass N (packetAtScale N k) = 1 := by
  classical
  simp [atomMass, packetAtScaleContainsAtom]

/-- For every finite number `N` of distinct scale labels, one unit of
atomic ledger mass funds all `N` nested packets, with only one packet at
each scale.  Consequently fixed-scale overlap one plus finite total measure
does not by itself bound cross-scale packet count. -/
theorem atomicLedgerFundsArbitrarilyManyNestedScales (N : ℕ) :
    ∃ totalMass : ℕ,
      totalMass = 1 ∧
      (Finset.univ : Finset (Fin N)).card = N ∧
      ∀ k : Fin N, atomMass N (packetAtScale N k) = totalMass := by
  refine ⟨1, rfl, by simp, ?_⟩
  intro k
  exact everyPacketHasFullAtomMass N k

#print axioms equalCellTotal
#print axioms noUniformSingleCellFraction
#print axioms typedZeroDoesNotImplyExternalZero
#print axioms firstThresholdDoesNotSupplyLowAncestor
#print axioms subthresholdScoreDoesNotImplySmallMass
#print axioms atomicLedgerFundsArbitrarilyManyNestedScales

end NavierStokesCoveringCountermodel
