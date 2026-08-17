import Mathlib

/-!
# Two-root polynomial-over-geometric envelope

A connected tree with `V` vertices has at most `V^2` ordered placements of two
passive roots.  This file proves, without strengthening the strict branch
condition `0 ≤ m < 1`, that the resulting polynomially marked geometric series
is uniformly summable.  More generally, any nonnegative placement weight
bounded by `(n+1)^2` inherits the same envelope.

This is finite real analysis and combinatorics.  It does not formalize the
replica--BKAR identity, Kirk's rooted Banach spaces, the six RG modules,
Yang--Mills theory, a mass gap, or a Clay theorem.
-/

open scoped BigOperators

namespace Millennium.YangMills.TwoRootGeometricEnvelope

/-- Exact nonnegative tail potential for the series
`∑ n, (n+1)^2 m^n`. -/
noncomputable def twoRootTail (m : ℝ) (n : ℕ) : ℝ :=
  m ^ n *
    ((((n : ℝ) + 1) ^ 2) / (1 - m) +
      2 * ((n : ℝ) + 1) * m / (1 - m) ^ 2 +
      m * (1 + m) / (1 - m) ^ 3)

/-- The tail potential telescopes by exactly one two-root placement term. -/
theorem twoRootTail_step
    (m : ℝ) (n : ℕ) (hm : m ≠ 1) :
    twoRootTail m n =
      (((n : ℝ) + 1) ^ 2) * m ^ n + twoRootTail m (n + 1) := by
  have hden : 1 - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hm)
  unfold twoRootTail
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp [hden]
  ring

/-- Every finite partial sum plus its exact tail equals the initial potential. -/
theorem partial_sum_add_twoRootTail
    (m : ℝ) (N : ℕ) (hm : m ≠ 1) :
    (∑ n ∈ Finset.range N, (((n : ℝ) + 1) ^ 2) * m ^ n) +
        twoRootTail m N =
      twoRootTail m 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hstep := twoRootTail_step m N hm
      linarith

/-- The exact tail potential is nonnegative throughout the strict branch
regime. -/
theorem twoRootTail_nonneg
    (m : ℝ) (n : ℕ) (hm0 : 0 ≤ m) (hm1 : m < 1) :
    0 ≤ twoRootTail m n := by
  have hden : 0 < 1 - m := sub_pos.mpr hm1
  unfold twoRootTail
  positivity

/-- The initial tail potential is the standard closed two-root envelope. -/
theorem twoRootTail_zero
    (m : ℝ) (hm : m ≠ 1) :
    twoRootTail m 0 = (1 + m) / (1 - m) ^ 3 := by
  have hden : 1 - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hm)
  unfold twoRootTail
  norm_num
  field_simp [hden]
  ring

/-- Uniform finite-depth bound for two ordered passive-root placements.  The
only threshold is the original geometric condition `m < 1`. -/
theorem finite_two_root_placement_bound
    (m : ℝ) (N : ℕ) (hm0 : 0 ≤ m) (hm1 : m < 1) :
    (∑ n ∈ Finset.range N, (((n : ℝ) + 1) ^ 2) * m ^ n) ≤
      (1 + m) / (1 - m) ^ 3 := by
  have hm_ne : m ≠ 1 := ne_of_lt hm1
  have hid := partial_sum_add_twoRootTail m N hm_ne
  have htail := twoRootTail_nonneg m N hm0 hm1
  have hzero := twoRootTail_zero m hm_ne
  calc
    (∑ n ∈ Finset.range N, (((n : ℝ) + 1) ^ 2) * m ^ n) ≤
        (∑ n ∈ Finset.range N, (((n : ℝ) + 1) ^ 2) * m ^ n) +
          twoRootTail m N := by linarith
    _ = twoRootTail m 0 := hid
    _ = (1 + m) / (1 - m) ^ 3 := hzero

/-- Any nonnegative fixed-root placement count bounded by `(n+1)^2` inherits
the same finite-depth envelope. -/
theorem finite_dominated_root_placement_bound
    (weight : ℕ → ℝ) (m : ℝ) (N : ℕ)
    (hweight0 : ∀ n, 0 ≤ weight n)
    (hweight2 : ∀ n, weight n ≤ ((n : ℝ) + 1) ^ 2)
    (hm0 : 0 ≤ m) (hm1 : m < 1) :
    (∑ n ∈ Finset.range N, weight n * m ^ n) ≤
      (1 + m) / (1 - m) ^ 3 := by
  calc
    (∑ n ∈ Finset.range N, weight n * m ^ n) ≤
        ∑ n ∈ Finset.range N, (((n : ℝ) + 1) ^ 2) * m ^ n := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right (hweight2 n) (pow_nonneg hm0 n)
    _ ≤ (1 + m) / (1 - m) ^ 3 :=
      finite_two_root_placement_bound m N hm0 hm1

/-- The two-root marked geometric series is summable for the full strict
interval `0 ≤ m < 1`. -/
theorem two_root_placement_summable
    (m : ℝ) (hm0 : 0 ≤ m) (hm1 : m < 1) :
    Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2) * m ^ n) := by
  apply summable_of_sum_range_le
  · intro n
    positivity
  · intro N
    exact finite_two_root_placement_bound m N hm0 hm1

/-- The infinite two-root placement mass obeys the same explicit envelope. -/
theorem two_root_placement_tsum_le
    (m : ℝ) (hm0 : 0 ≤ m) (hm1 : m < 1) :
    (∑' n : ℕ, (((n : ℝ) + 1) ^ 2) * m ^ n) ≤
      (1 + m) / (1 - m) ^ 3 := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    positivity
  · intro N
    exact finite_two_root_placement_bound m N hm0 hm1

/-- Any nonnegative placement count dominated by the two-root count is
summable under exactly the same branch condition. -/
theorem dominated_root_placement_summable
    (weight : ℕ → ℝ) (m : ℝ)
    (hweight0 : ∀ n, 0 ≤ weight n)
    (hweight2 : ∀ n, weight n ≤ ((n : ℝ) + 1) ^ 2)
    (hm0 : 0 ≤ m) (hm1 : m < 1) :
    Summable (fun n : ℕ => weight n * m ^ n) := by
  apply summable_of_sum_range_le
  · intro n
    exact mul_nonneg (hweight0 n) (pow_nonneg hm0 n)
  · intro N
    exact finite_dominated_root_placement_bound
      weight m N hweight0 hweight2 hm0 hm1

/-- The corresponding infinite dominated placement mass has the same explicit
bound. -/
theorem dominated_root_placement_tsum_le
    (weight : ℕ → ℝ) (m : ℝ)
    (hweight0 : ∀ n, 0 ≤ weight n)
    (hweight2 : ∀ n, weight n ≤ ((n : ℝ) + 1) ^ 2)
    (hm0 : 0 ≤ m) (hm1 : m < 1) :
    (∑' n : ℕ, weight n * m ^ n) ≤
      (1 + m) / (1 - m) ^ 3 := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    exact mul_nonneg (hweight0 n) (pow_nonneg hm0 n)
  · intro N
    exact finite_dominated_root_placement_bound
      weight m N hweight0 hweight2 hm0 hm1

#print axioms twoRootTail_step
#print axioms partial_sum_add_twoRootTail
#print axioms twoRootTail_nonneg
#print axioms twoRootTail_zero
#print axioms finite_two_root_placement_bound
#print axioms finite_dominated_root_placement_bound
#print axioms two_root_placement_summable
#print axioms two_root_placement_tsum_le
#print axioms dominated_root_placement_summable
#print axioms dominated_root_placement_tsum_le

end Millennium.YangMills.TwoRootGeometricEnvelope
