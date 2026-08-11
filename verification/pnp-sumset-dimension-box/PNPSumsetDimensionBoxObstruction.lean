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

/--
A padded description of a sum of at most `ℓ` rows. `none` is an unused slot;
`some i` contributes row `i`. This includes the empty sum, which only enlarges
the represented image and therefore is harmless for an upper bound.
-/
abbrev SumDescription (m ℓ : ℕ) := Fin ℓ → Option (Fin m)

/-- One coordinate contributed by an optional row. -/
def optionalCoeff {m d : ℕ}
    (A : Fin m → Fin d → ℕ)
    (row : Option (Fin m))
    (j : Fin d) : ℕ :=
  match row with
  | none => 0
  | some i => A i j

/-- The evaluated contribution of an optional row. -/
def optionalEval {m d : ℕ}
    (A : Fin m → Fin d → ℕ)
    (beta : Fin d → ℕ)
    (row : Option (Fin m)) : ℕ :=
  ∑ j, optionalCoeff A row j * beta j

/-- Every optional-row coefficient is bounded by `M`. -/
theorem optionalCoeff_le
    {m d M : ℕ}
    (A : Fin m → Fin d → ℕ)
    (hA : ∀ i j, A i j ≤ M)
    (row : Option (Fin m))
    (j : Fin d) :
    optionalCoeff A row j ≤ M := by
  cases row with
  | none => simp [optionalCoeff]
  | some i => simpa [optionalCoeff] using hA i j

/-- Evaluate a padded row-sum description. -/
def sumDescriptionEval
    {m d ℓ : ℕ}
    (A : Fin m → Fin d → ℕ)
    (beta : Fin d → ℕ)
    (q : SumDescription m ℓ) : ℕ :=
  ∑ t, optionalEval A beta (q t)

/-- The aggregate exponent in coordinate `j` of a padded description. -/
def descriptionCoeffNat
    {m d ℓ : ℕ}
    (A : Fin m → Fin d → ℕ)
    (q : SumDescription m ℓ)
    (j : Fin d) : ℕ :=
  ∑ t, optionalCoeff A (q t) j

/-- Description evaluation factors through its aggregate coefficient vector. -/
theorem sumDescriptionEval_eq_eval_descriptionCoeffNat
    {m d ℓ : ℕ}
    (A : Fin m → Fin d → ℕ)
    (beta : Fin d → ℕ)
    (q : SumDescription m ℓ) :
    sumDescriptionEval A beta q =
      ∑ j, descriptionCoeffNat A q j * beta j := by
  classical
  calc
    sumDescriptionEval A beta q
        = ∑ t, ∑ j, optionalCoeff A (q t) j * beta j := by rfl
    _ = ∑ j, ∑ t, optionalCoeff A (q t) j * beta j := by
      exact Finset.sum_comm
    _ = ∑ j, (∑ t, optionalCoeff A (q t) j) * beta j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ = ∑ j, descriptionCoeffNat A q j * beta j := by rfl

/-- Every aggregate description coefficient is at most `ℓ*M`. -/
theorem descriptionCoeffNat_le
    {m d ℓ M : ℕ}
    (A : Fin m → Fin d → ℕ)
    (hA : ∀ i j, A i j ≤ M)
    (q : SumDescription m ℓ)
    (j : Fin d) :
    descriptionCoeffNat A q j ≤ ℓ * M := by
  classical
  unfold descriptionCoeffNat
  calc
    (∑ t, optionalCoeff A (q t) j) ≤ ∑ _t : Fin ℓ, M := by
      apply Finset.sum_le_sum
      intro t _
      exact optionalCoeff_le A hA (q t) j
    _ = ℓ * M := by simp

/-- Encode a padded description by its bounded aggregate coefficient vector. -/
def boundedDescriptionCoeff
    {m d ℓ M : ℕ}
    (A : Fin m → Fin d → ℕ)
    (hA : ∀ i j, A i j ≤ M)
    (q : SumDescription m ℓ) :
    CoeffBox d (ℓ * M) :=
  fun j =>
    ⟨descriptionCoeffNat A q j,
      Nat.lt_succ_of_le (descriptionCoeffNat_le A hA q j)⟩

/-- The bounded description encoding evaluates to the represented row sum. -/
theorem boxEval_boundedDescriptionCoeff_eq
    {m d ℓ M : ℕ}
    (A : Fin m → Fin d → ℕ)
    (beta : Fin d → ℕ)
    (hA : ∀ i j, A i j ≤ M)
    (q : SumDescription m ℓ) :
    boxEval beta (boundedDescriptionCoeff A hA q) =
      sumDescriptionEval A beta q := by
  rw [sumDescriptionEval_eq_eval_descriptionCoeffNat]
  rfl

/--
**Dimension-box bound.** The number of values represented by padded sums of at
most `ℓ` rows is at most `(ℓ*M+1)^d`, independently of `beta` and of `m`.
Consequently the positive-length union `ℓ^{≤} A^beta` obeys the same bound.
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
    exact ⟨boundedDescriptionCoeff A hA q, Finset.mem_univ _,
      boxEval_boundedDescriptionCoeff_eq A beta hA q⟩
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
#print axioms optionalCoeff_le
#print axioms sumDescriptionEval_eq_eval_descriptionCoeffNat
#print axioms descriptionCoeffNat_le
#print axioms boxEval_boundedDescriptionCoeff_eq
#print axioms bounded_evaluated_sumset_card_le
#print axioms expander_capacity_bound
#print axioms no_expansion_above_dimension_box
#print axioms power_capacity_forces_exponent_le
#print axioms theorem4_exponent_budget

end SumsetDimensionBoxObstruction
end PNP
