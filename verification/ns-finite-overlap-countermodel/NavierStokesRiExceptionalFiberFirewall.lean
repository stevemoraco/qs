import Mathlib

namespace NavierStokesRiExceptionalFiberFirewall

/-- A constant weight repeated on `N` domain points contributes `N * B`, not
one copy of `B`.  This is the finite multiplicity identity omitted when a sum
over frequency thresholds is bounded by the cardinality of its image set. -/
theorem repeatedFiberWeightSum (N : ℕ) (B : ℝ) :
    Finset.sum (Finset.range N) (fun _ => B) = (N : ℝ) * B := by
  simp

/-- The cardinality of a one-point image cannot bound a positive weighted sum
on a nontrivial fiber.  A many-to-one map requires a fiber-multiplicity factor. -/
theorem imageCardinalityDoesNotBoundRepeatedFiber
    (N : ℕ) (B : ℝ)
    (hN : 1 < N)
    (hB : 0 < B) :
    B < Finset.sum (Finset.range N) (fun _ => B) := by
  rw [repeatedFiberWeightSum]
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN
  nlinarith

/-- A linear prefix bound on a block occupying half of the prefix forces the
block weight itself to be uniformly bounded.  The fiber multiplicity cancels
only after it has first been included. -/
theorem halfFiberLinearBoundForcesWeightBound
    (N : ℕ) (B C : ℝ)
    (hN : 0 < N)
    (haverage : (N : ℝ) * B ≤ C * (2 * (N : ℝ))) :
    B ≤ 2 * C := by
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast hN
  nlinarith

/-- If the exponentially weighted average has spike floor `A/2`, while the
corresponding dyadic fiber occupies half of a prefix with linear-average
constant `C`, then necessarily `A ≤ 4C`.  Thus unbounded scaling spikes and a
uniform linear threshold average are structurally incompatible. -/
theorem spikeGrowthIncompatibleWithUniformLinearAverage
    (N : ℕ) (A B C : ℝ)
    (hN : 0 < N)
    (hspike : A / 2 ≤ B)
    (haverage : (N : ℝ) * B ≤ C * (2 * (N : ℝ))) :
    A ≤ 4 * C := by
  have hB := halfFiberLinearBoundForcesWeightBound N B C hN haverage
  linarith

/-- If an exceptional dyadic block occupies half of all thresholds up to `n`
and every threshold in that block has weight at least eight, then the
exceptional block alone contributes more than `3n`.

In Ri's notation at the fourth sparse spike, the block cardinality is
`N = 2^(m-3)`, the total threshold count is `n = 2N`, and the source-defined
weight satisfies `b(m) ≥ 8`. -/
theorem weightEightHalfBlockExceedsThreeTotal
    (N : ℕ)
    (hN : 0 < N) :
    3 * (2 * (N : ℝ)) < (N : ℝ) * 8 := by
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast hN
  nlinarith

/-- Weighted version of the source-specific block contradiction.  If every
member of a block of cardinality `N` has weight at least eight, its sum is
strictly larger than three times a total count of `2N`. -/
theorem exceptionalBlockOverrunsClaimedLinearBound
    (N : ℕ)
    (weight : ℕ → ℝ)
    (hN : 0 < N)
    (hweight : ∀ k < N, 8 ≤ weight k) :
    3 * (2 * (N : ℝ)) < Finset.sum (Finset.range N) weight := by
  have hsum :
      Finset.sum (Finset.range N) (fun _ => (8 : ℝ)) ≤
        Finset.sum (Finset.range N) weight := by
    apply Finset.sum_le_sum
    intro k hk
    exact hweight k (Finset.mem_range.mp hk)
  have hconst :
      Finset.sum (Finset.range N) (fun _ => (8 : ℝ)) =
        (N : ℝ) * 8 := by
    simp
  have hover := weightEightHalfBlockExceedsThreeTotal N hN
  rw [hconst] at hsum
  linarith

/-- Merely knowing that every repeated threshold maps into one exceptional
index does not make the threshold map injective.  This explicit four-to-one
model has image cardinality one and positive image weight eight, while the
preimage sum is thirty-two. -/
theorem fourToOneExceptionalImageCountermodel :
    let index : Fin 4 → Fin 1 := fun _ => 0
    let weight : Fin 1 → ℝ := fun _ => 8
    Fintype.card (Fin 1) = 1 ∧
    (∑ k : Fin 4, weight (index k)) = 32 ∧
    (∑ k : Fin 4, weight (index k)) >
      (Fintype.card (Fin 1) : ℝ) * 8 := by
  norm_num

#print axioms repeatedFiberWeightSum
#print axioms imageCardinalityDoesNotBoundRepeatedFiber
#print axioms halfFiberLinearBoundForcesWeightBound
#print axioms spikeGrowthIncompatibleWithUniformLinearAverage
#print axioms weightEightHalfBlockExceedsThreeTotal
#print axioms exceptionalBlockOverrunsClaimedLinearBound
#print axioms fourToOneExceptionalImageCountermodel

end NavierStokesRiExceptionalFiberFirewall
