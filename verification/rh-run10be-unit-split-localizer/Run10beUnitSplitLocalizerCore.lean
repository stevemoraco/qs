import Mathlib

namespace Millennium.RH

/--
The Run10be unit-shift split localizer.

For the intended source split `Y = A + B`, a pointwise cap
`Y <= 101/100` makes this witness nonnegative.
-/
def run10beWitness (A B : ℝ) : ℝ :=
  (A + 1) ^ 2 *
    ((101 / 100 : ℝ) - (A + B)) *
      (B + 1) ^ 2

/-- Pointwise cap positivity for the unit split localizer. -/
theorem run10be_witness_nonneg_of_cap
    (A B : ℝ)
    (hcap : A + B ≤ (101 / 100 : ℝ)) :
    0 ≤ run10beWitness A B := by
  unfold run10beWitness
  have hA : 0 ≤ (A + 1) ^ 2 := sq_nonneg _
  have hgap : 0 ≤ (101 / 100 : ℝ) - (A + B) := by linarith
  have hB : 0 ≤ (B + 1) ^ 2 := sq_nonneg _
  exact mul_nonneg (mul_nonneg hA hgap) hB

/--
A negative nonnegatively weighted finite average of the unit witness forces an
actual threshold violation at one sampled point.

This is only finite order algebra.  The natural-window integral statement is
an analytic analogue and is deliberately not hidden here.
-/
theorem run10be_negative_weighted_average_forces_tail
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (weight A B : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ weight i)
    (hneg :
      ∑ i ∈ s, weight i * run10beWitness (A i) (B i) < 0) :
    ∃ i ∈ s, (101 / 100 : ℝ) < A i + B i := by
  by_contra htail
  have hcap : ∀ i ∈ s, A i + B i ≤ (101 / 100 : ℝ) := by
    intro i hi
    exact le_of_not_gt (by
      intro hgt
      exact htail ⟨i, hi, hgt⟩)
  have hsum :
      0 ≤ ∑ i ∈ s, weight i * run10beWitness (A i) (B i) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hw i hi)
      (run10be_witness_nonneg_of_cap (A i) (B i) (hcap i hi))
  exact (not_lt_of_ge hsum) hneg

/--
The unit witness is the cap gap times one exact square:
`(q-Y) * ((1+A)(1+B))^2`, with `Y=A+B`.
-/
theorem run10be_witness_factorization (A B : ℝ) :
    run10beWitness A B =
      ((101 / 100 : ℝ) - (A + B)) *
        ((1 + A) * (1 + B)) ^ 2 := by
  unfold run10beWitness
  ring

/-- Exact degree-five polynomial expansion of the unit witness. -/
theorem run10be_witness_expansion (A B : ℝ) :
    run10beWitness A B =
      -A ^ 3 * B ^ 2
      - 2 * A ^ 3 * B
      - A ^ 3
      - A ^ 2 * B ^ 3
      - (299 / 100 : ℝ) * A ^ 2 * B ^ 2
      - (149 / 50 : ℝ) * A ^ 2 * B
      - (99 / 100 : ℝ) * A ^ 2
      - 2 * A * B ^ 3
      - (149 / 50 : ℝ) * A * B ^ 2
      + (1 / 25 : ℝ) * A * B
      + (51 / 50 : ℝ) * A
      - B ^ 3
      - (99 / 100 : ℝ) * B ^ 2
      + (51 / 50 : ℝ) * B
      + (101 / 100 : ℝ) := by
  unfold run10beWitness
  ring

/-- Ideal Bohr localizer mass: `(5/4)(7/4)=35/16`. -/
theorem run10be_ideal_weight_mass :
    (5 / 4 : ℝ) * (7 / 4 : ℝ) = (35 / 16 : ℝ) := by
  norm_num

/--
Ideal Bohr `Y`-weighted numerator from the two independent split blocks.
The first block contributes `(1/2)(7/4)` and the second `(5/4)(3/2)`.
-/
theorem run10be_ideal_weighted_numerator :
    (1 / 2 : ℝ) * (7 / 4 : ℝ) +
        (5 / 4 : ℝ) * (3 / 2 : ℝ) =
      (11 / 4 : ℝ) := by
  norm_num

/-- Exact ideal weighted mean of `Y`: `(11/4)/(35/16)=44/35`. -/
theorem run10be_ideal_weighted_ratio :
    (11 / 4 : ℝ) / (35 / 16 : ℝ) = (44 / 35 : ℝ) := by
  norm_num

/-- The ideal weighted mean clears the target `101/100` by `173/700`. -/
theorem run10be_ideal_ratio_gap :
    (44 / 35 : ℝ) - (101 / 100 : ℝ) = (173 / 700 : ℝ) := by
  norm_num

/-- Exact ideal unit-witness mean: `-173/320`. -/
theorem run10be_ideal_witness_margin :
    (101 / 100 : ℝ) * (35 / 16 : ℝ) - (11 / 4 : ℝ)
      = -(173 / 320 : ℝ) := by
  norm_num

/--
The corresponding ideal order-one localizer determinant is strictly negative.
The entries are `S0=61/80`, `S1=-15/16`, `S2=183/320`.
-/
theorem run10be_ideal_localizer_determinant :
    (61 / 80 : ℝ) * (183 / 320 : ℝ) - (-15 / 16 : ℝ) ^ 2
      = -(11337 / 25600 : ℝ) := by
  norm_num

/--
The unit-shift ideal reserve is strictly more negative than Run10bd's
`-4899/13600` reserve.  This comparison is finite rational arithmetic only.
-/
theorem run10be_reserve_strictly_improves_run10bd :
    -(173 / 320 : ℝ) < -(4899 / 13600 : ℝ) := by
  norm_num

/-- Exact difference between the Run10be and Run10bd ideal reserves. -/
theorem run10be_reserve_difference :
    -(173 / 320 : ℝ) - (-(4899 / 13600 : ℝ))
      = -(4907 / 27200 : ℝ) := by
  norm_num

#print axioms run10be_witness_nonneg_of_cap
#print axioms run10be_negative_weighted_average_forces_tail
#print axioms run10be_witness_factorization
#print axioms run10be_witness_expansion
#print axioms run10be_ideal_weight_mass
#print axioms run10be_ideal_weighted_numerator
#print axioms run10be_ideal_weighted_ratio
#print axioms run10be_ideal_ratio_gap
#print axioms run10be_ideal_witness_margin
#print axioms run10be_ideal_localizer_determinant
#print axioms run10be_reserve_strictly_improves_run10bd
#print axioms run10be_reserve_difference

end Millennium.RH
