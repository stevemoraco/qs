import Mathlib

/-!
# P versus NP: evaluated-sumset dimension-box obstruction

This file formalizes the finite combinatorial core of an obstruction for
sumset-expansion constructions based on bounded nonnegative exponent matrices.

For a `d`-coordinate exponent matrix with entries at most `M`, every sum of at
most `ℓ` evaluated rows is determined by a coefficient vector in
`{0, ..., ℓ*M}^d`.  Hence the number of distinct evaluated sums is at most
`(ℓ*M + 1)^d`, independently of the size of the auxiliary evaluation vector.

The file does **not** formalize arithmetic circuits, elusive functions,
poly-definability, VP versus VNP, or P versus NP.
-/

namespace PNP
namespace SumsetDimensionBoxObstruction

/-- The coefficient box `{0, ..., B}^d`. -/
abbrev CoeffBox (d B : ℕ) := Fin d → Fin (B + 1)

/-- The coefficient box has exactly `(B+1)^d` elements. -/
theorem coeffBox_card (d B : ℕ) :
    Fintype.card (CoeffBox d B) = (B + 1) ^ d := by
  simp [CoeffBox]

/-- Evaluate a bounded coefficient vector against an arbitrary auxiliary vector. -/
def boxEval {d B : ℕ} (beta : Fin d → ℕ) (v : CoeffBox d B) : ℕ :=
  ∑ j, (v j).val * beta j

/-- An arbitrary evaluation map cannot have a larger image than its coefficient box. -/
theorem box_evaluation_image_card_le
    (d B : ℕ)
    (beta : Fin d → ℕ) :
    (Finset.univ.image (boxEval beta : CoeffBox d B → ℕ)).card ≤
      (B + 1) ^ d := by
  calc
    (Finset.univ.image (boxEval beta : CoeffBox d B → ℕ)).card
        ≤ (Finset.univ : Finset (CoeffBox d B)).card := Finset.card_image_le
    _ = (B + 1) ^ d := by simp [CoeffBox]

/-- Evaluate one row of a nonnegative exponent matrix. -/
def rowEval {m d : ℕ}
    (A : Fin m → Fin d → ℕ)
    (beta : Fin d → ℕ)
    (i : Fin m) : ℕ :=
  ∑ j, A i j * beta j

/-- Coordinatewise coefficient sum of a finite sequence of matrix rows. -/
def rowCoeff {m d k : ℕ}
    (A : Fin m → Fin d → ℕ)
    (rows : Fin k → Fin m)
    (j : Fin d) : ℕ :=
  ∑ t, A (rows t) j

/-- Summing evaluated rows equals evaluating their coordinatewise coefficient sum. -/
theorem sum_rowEval_eq_eval_rowCoeff
    {m d k : ℕ}
    (A : Fin m → Fin d → ℕ)
    (beta : Fin d → ℕ)
    (rows : Fin k → Fin m) :
    (∑ t, rowEval A beta (rows t)) =
      ∑ j, rowCoeff A rows j * beta j := by
  classical
  calc
    (∑ t, rowEval A beta (rows t))
        = ∑ t, ∑ j, A (rows t) j * beta j := by rfl
    _ = ∑ j, ∑ t, A (rows t) j * beta j := by
      exact Finset.sum_comm
    _ = ∑ j, (∑ t, A (rows t) j) * beta j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ = ∑ j, rowCoeff A rows j * beta j := by rfl

/-- A length-`k` row sum has every coefficient at most `k*M`. -/
theorem rowCoeff_le_length_mul
    {m d k M : ℕ}
    (A : Fin m → Fin d → ℕ)
    (rows : Fin k → Fin m)
    (hA : ∀ i j, A i j ≤ M)
    (j : Fin d) :
    rowCoeff A rows j ≤ k * M := by
  classical
  unfold rowCoeff
  calc
    (∑ t, A (rows t) j) ≤ ∑ _t : Fin k, M := by
      apply Finset.sum_le_sum
      intro t _
      exact hA (rows t) j
    _ = k * M := by simp

/-- If `k ≤ ℓ`, the row-sum coefficient lies in `{0, ..., ℓ*M}`. -/
theorem rowCoeff_le_iteration_box
    {m d k ℓ M : ℕ}
    (A : Fin m → Fin d → ℕ)
    (rows : Fin k → Fin m)
    (hA : ∀ i j, A i j ≤ M)
    (hk : k ≤ ℓ)
    (j : Fin d) :
    rowCoeff A rows j ≤ ℓ * M := by
  exact (rowCoeff_le_length_mul A rows hA j).trans
    (Nat.mul_le_mul_right M hk)

/-- Encode a row sum of length at most `ℓ` by its bounded coefficient vector. -/
def boundedRowCoeff
    {m d k ℓ M : ℕ}
    (A : Fin m → Fin d → ℕ)
    (rows : Fin k → Fin m)
    (hA : ∀ i j, A i j ≤ M)
    (hk : k ≤ ℓ) :
    CoeffBox d (ℓ * M) :=
  fun j =>
    ⟨rowCoeff A rows j,
      Nat.lt_succ_of_le (rowCoeff_le_iteration_box A rows hA hk j)⟩

/-- The bounded coefficient encoding evaluates to the original row sum. -/
theorem boxEval_boundedRowCoeff_eq_sum_rowEval
    {m d k ℓ M : ℕ}
    (A : Fin m → Fin d → ℕ)
    (beta : Fin d → ℕ)
    (rows : Fin k → Fin m)
    (hA : ∀ i j, A i j ≤ M)
    (hk : k ≤ ℓ) :
    boxEval beta (boundedRowCoeff A rows hA hk) =
      ∑ t, rowEval A beta (rows t) := by
  rw [sum_rowEval_eq_eval_rowCoeff]
  rfl

/-- A description consists of a positive length `k ≤ ℓ` and a sequence of `k` rows. -/
def SumDescription (m ℓ : ℕ) :=
  Σ k : Fin ℓ, Fin (k.val + 1) → Fin m

/-- The dependent description type is finite. -/
noncomputable instance sumDescriptionFintype (m ℓ : ℕ) :
    Fintype (SumDescription m ℓ) :=
  Fintype.ofFinite (SumDescription m ℓ)

/-- The evaluated sum represented by a positive-length row description. -/
def sumDescriptionEval
    {m d ℓ : ℕ}
    (A : Fin m → Fin d → ℕ)
    (beta : Fin d → ℕ)
    (q : SumDescription m ℓ) : ℕ :=
  ∑ t, rowEval A beta (q.2 t)

/-- The bounded coefficient vector attached to a row-sum description. -/
def descriptionCoeff
    {m d ℓ M : ℕ}
    (A : Fin m → Fin d → ℕ)
    (hA : ∀ i j, A i j ≤ M)
    (q : SumDescription m ℓ) :
    CoeffBox d (ℓ * M) :=
  boundedRowCoeff A q.2 hA q.1.isLt

/-- Description evaluation factors through the coefficient box. -/
theorem boxEval_descriptionCoeff_eq
    {m d ℓ M : ℕ}
    (A : Fin m → Fin d → ℕ)
    (beta : Fin d → ℕ)
    (hA : ∀ i j, A i j ≤ M)
    (q : SumDescription m ℓ) :
    boxEval beta (descriptionCoeff A hA q) =
      sumDescriptionEval A beta q := by
  exact boxEval_boundedRowCoeff_eq_sum_rowEval
    A beta q.2 hA q.1.isLt

/--
**Dimension-box bound.**  The number of distinct sums of between one and `ℓ`
evaluated rows is at most `(ℓ*M+1)^d`, independently of `beta` and of the
number of rows `m`.
-/
theorem bounded_evaluated_sumset_card_le
    {m d ℓ M : ℕ}
    (A : Fin m → Fin d → ℕ)
    (beta : Fin d → ℕ)
    (hA : ∀ i j, A i j ≤ M) :
    (Finset.univ.image (sumDescriptionEval A beta : SumDescription m ℓ → ℕ)).card
      ≤ (ℓ * M + 1) ^ d := by
  classical
  have hsubset :
      Finset.univ.image (sumDescriptionEval A beta : SumDescription m ℓ → ℕ) ⊆
        Finset.univ.image (boxEval beta : CoeffBox d (ℓ * M) → ℕ) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨q, _hq, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨descriptionCoeff A hA q, Finset.mem_univ _,
      boxEval_descriptionCoeff_eq A beta hA q⟩
  calc
    (Finset.univ.image (sumDescriptionEval A beta : SumDescription m ℓ → ℕ)).card
        ≤ (Finset.univ.image (boxEval beta : CoeffBox d (ℓ * M) → ℕ)).card :=
      Finset.card_le_card hsubset
    _ ≤ (ℓ * M + 1) ^ d := box_evaluation_image_card_le d (ℓ * M) beta

/-- Any claimed expansion lower bound is capped by the dimension box. -/
theorem expander_capacity_bound
    {m d ℓ M C : ℕ}
    (A : Fin m → Fin d → ℕ)
    (beta : Fin d → ℕ)
    (hA : ∀ i j, A i j ≤ M)
    (hExpand : C ≤
      (Finset.univ.image
        (sumDescriptionEval A beta : SumDescription m ℓ → ℕ)).card) :
    C ≤ (ℓ * M + 1) ^ d := by
  exact hExpand.trans (bounded_evaluated_sumset_card_le A beta hA)

/-- If the target exceeds the box capacity, no bounded exponent matrix can attain it. -/
theorem no_expansion_above_dimension_box
    {m d ℓ M C : ℕ}
    (A : Fin m → Fin d → ℕ)
    (beta : Fin d → ℕ)
    (hA : ∀ i j, A i j ≤ M)
    (hTooLarge : (ℓ * M + 1) ^ d < C) :
    ¬ C ≤
      (Finset.univ.image
        (sumDescriptionEval A beta : SumDescription m ℓ → ℕ)).card := by
  intro hExpand
  have hcap := expander_capacity_bound A beta hA hExpand
  omega

/-- For base at least two, a power-capacity inequality forces the exponent inequality. -/
theorem power_capacity_forces_exponent_le
    (n lowerExponent upperExponent : ℕ)
    (hn : 2 ≤ n)
    (hpow : n ^ lowerExponent ≤ n ^ upperExponent) :
    lowerExponent ≤ upperExponent := by
  by_contra hnot
  have hexp : upperExponent < lowerExponent := Nat.lt_of_not_ge hnot
  have hpowers : n ^ upperExponent < n ^ lowerExponent :=
    Nat.pow_lt_pow_right (by omega) hexp
  omega

/--
The exponent extraction used after bounding a target `n^(8*s)` by a capacity
`n^((K+4)*d)`.
-/
theorem theorem4_exponent_budget
    (n s d K : ℕ)
    (hn : 2 ≤ n)
    (hcapacity : n ^ (8 * s) ≤ n ^ ((K + 4) * d)) :
    8 * s ≤ (K + 4) * d := by
  exact power_capacity_forces_exponent_le
    n (8 * s) ((K + 4) * d) hn hcapacity

#print axioms coeffBox_card
#print axioms box_evaluation_image_card_le
#print axioms sum_rowEval_eq_eval_rowCoeff
#print axioms rowCoeff_le_length_mul
#print axioms rowCoeff_le_iteration_box
#print axioms boxEval_boundedRowCoeff_eq_sum_rowEval
#print axioms boxEval_descriptionCoeff_eq
#print axioms bounded_evaluated_sumset_card_le
#print axioms expander_capacity_bound
#print axioms no_expansion_above_dimension_box
#print axioms power_capacity_forces_exponent_le
#print axioms theorem4_exponent_budget

end SumsetDimensionBoxObstruction
end PNP
