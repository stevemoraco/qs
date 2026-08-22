import BSDGVSemiprimeDensity

/-!
# Exact information frontier after forgetting the Legendre-symbol bit

The finite Ghosh--Voutier state space has 64 ordered residue pairs modulo 16.
Exactly two pairs accept both Legendre signs, 24 accept one sign, and 38 accept
neither sign. A residue-only selector therefore chooses some number `d` of
double-hit pairs, `s` of single-hit pairs, and `z` of zero-hit pairs.

This file proves the complete finite precision--recall frontier determined by
those three capacities. It is an information-loss theorem, not a BSD theorem:
the arithmetic identification of the three classes is supplied by the finite
state module, while prime distribution, Selmer theory, and BSD remain outside
this formal core.
-/

namespace BSDGVSemiprimeDensity

/-- Number of selected ordered residue pairs. -/
def selectorPairCount (d s z : Nat) : Nat := d + s + z

/-- Number of selected residue/sign states that are genuinely accepted. -/
def selectorTruePositives (d s : Nat) : Nat := 2 * d + s

/-- Number of selected residue/sign states that are false positives. -/
def selectorFalsePositives (s z : Nat) : Nat := s + 2 * z

/-- Every selected residue pair restores both possible Legendre signs. -/
def selectorStateCount (d s z : Nat) : Nat := 2 * selectorPairCount d s z

/-- The sharp pointwise upper envelope for true positives at a fixed selected
pair count `k`. The three cuts are respectively: two signs per pair, only two
double-hit pairs, and only 28 accepted states in total. -/
def selectorTruePositiveEnvelope (k : Nat) : Nat :=
  Nat.min (2 * k) (Nat.min (k + 2) 28)

/-- Selected states partition exactly into true and false positives. -/
theorem selector_state_partition (d s z : Nat) :
    selectorStateCount d s z =
      selectorTruePositives d s + selectorFalsePositives s z := by
  simp [selectorStateCount, selectorPairCount, selectorTruePositives,
    selectorFalsePositives]
  omega

/-- Complete upper frontier. The hypotheses encode the exact capacities
`2` double-hit, `24` single-hit, and `38` zero-hit residue pairs. -/
theorem selector_true_positive_frontier
    (d s z : Nat) (hd : d ≤ 2) (hs : s ≤ 24) :
    selectorTruePositives d s ≤
      selectorTruePositiveEnvelope (selectorPairCount d s z) := by
  unfold selectorTruePositiveEnvelope
  apply le_min
  · simp [selectorTruePositives, selectorPairCount]
    omega
  · apply le_min
    · simp [selectorTruePositives, selectorPairCount]
      omega
    · simp [selectorTruePositives]
      omega

/-- The first false-positive floor: after selecting at least two residue pairs,
every additional selected pair forces at least one false-positive sign state. -/
theorem selector_false_positive_floor_middle
    (d s z : Nat) (hd : d ≤ 2)
    (hk : 2 ≤ selectorPairCount d s z) :
    selectorPairCount d s z - 2 ≤ selectorFalsePositives s z := by
  simp [selectorPairCount, selectorFalsePositives] at *
  omega

/-- The second false-positive floor: after the 26 residue pairs containing all
28 accepted states have been selected, each additional pair contributes two
false positives. -/
theorem selector_false_positive_floor_high
    (d s z : Nat) (hd : d ≤ 2) (hs : s ≤ 24)
    (hk : 26 ≤ selectorPairCount d s z) :
    2 * selectorPairCount d s z - 28 ≤ selectorFalsePositives s z := by
  simp [selectorPairCount, selectorFalsePositives] at *
  omega

/-- Zero false positives force the selector to use only the two double-hit
pairs. It can recover at most four of the 28 accepted sign states, i.e. recall
at most `1/7`. The cross-multiplied recall certificate is included. -/
theorem zero_false_positive_recall_ceiling
    (d s z : Nat) (hd : d ≤ 2)
    (hzero : selectorFalsePositives s z = 0) :
    selectorTruePositives d s ≤ 4 ∧
      7 * selectorTruePositives d s ≤ 28 := by
  simp [selectorFalsePositives, selectorTruePositives] at *
  omega

/-- Perfect recall forces selection of both double-hit pairs and all 24
single-hit pairs. Hence at least 26 residue pairs, 52 sign states, and 24 false
positives are unavoidable. The final inequality is the exact precision ceiling
`28/52 = 7/13` in cross-multiplied form. -/
theorem perfect_recall_precision_ceiling
    (d s z : Nat) (hd : d ≤ 2) (hs : s ≤ 24)
    (hrec : selectorTruePositives d s = 28) :
    d = 2 ∧ s = 24 ∧
      26 ≤ selectorPairCount d s z ∧
      52 ≤ selectorStateCount d s z ∧
      24 ≤ selectorFalsePositives s z ∧
      13 * selectorTruePositives d s ≤ 7 * selectorStateCount d s z := by
  simp [selectorTruePositives, selectorPairCount, selectorStateCount,
    selectorFalsePositives] at *
  omega

/-- The low-support branch of the frontier is attained for every `k ≤ 2` by
selecting `k` double-hit pairs. -/
theorem selector_frontier_attained_low (k : Nat) (hk : k ≤ 2) :
    ∃ d s z,
      d ≤ 2 ∧ s ≤ 24 ∧ z ≤ 38 ∧
      selectorPairCount d s z = k ∧
      selectorTruePositives d s = 2 * k := by
  refine ⟨k, 0, 0, hk, by omega, by omega, ?_, ?_⟩
  · simp [selectorPairCount]
  · simp [selectorTruePositives]

/-- The middle branch is attained for every `2 ≤ k ≤ 26` by selecting both
double-hit pairs and `k-2` single-hit pairs. -/
theorem selector_frontier_attained_middle
    (k : Nat) (hlo : 2 ≤ k) (hhi : k ≤ 26) :
    ∃ d s z,
      d ≤ 2 ∧ s ≤ 24 ∧ z ≤ 38 ∧
      selectorPairCount d s z = k ∧
      selectorTruePositives d s = k + 2 := by
  refine ⟨2, k - 2, 0, by omega, by omega, by omega, ?_, ?_⟩
  · simp [selectorPairCount]
    omega
  · simp [selectorTruePositives]
    omega

/-- The high-support branch is attained for every `26 ≤ k ≤ 64` by selecting
all 26 accepted residue pairs and `k-26` zero-hit pairs. -/
theorem selector_frontier_attained_high
    (k : Nat) (hlo : 26 ≤ k) (hhi : k ≤ 64) :
    ∃ d s z,
      d ≤ 2 ∧ s ≤ 24 ∧ z ≤ 38 ∧
      selectorPairCount d s z = k ∧
      selectorTruePositives d s = 28 := by
  refine ⟨2, 24, k - 26, by omega, by omega, by omega, ?_, ?_⟩
  · simp [selectorPairCount]
    omega
  · simp [selectorTruePositives]

#print axioms selector_state_partition
#print axioms selector_true_positive_frontier
#print axioms selector_false_positive_floor_middle
#print axioms selector_false_positive_floor_high
#print axioms zero_false_positive_recall_ceiling
#print axioms perfect_recall_precision_ceiling
#print axioms selector_frontier_attained_low
#print axioms selector_frontier_attained_middle
#print axioms selector_frontier_attained_high

end BSDGVSemiprimeDensity