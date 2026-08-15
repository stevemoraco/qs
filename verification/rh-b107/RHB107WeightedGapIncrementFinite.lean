import Mathlib

/-!
# RH B107 weighted prime-gap increment finite core

Finite real/order algebra only.  This file formalizes the load-bearing finite
steps in the B107 weighted positive-variation and selector/negative-depth
repackaging.  It deliberately does not formalize primes, Stadlmann's gap theorem,
the B46 explicit formula, the B73 Landau bridge, matrices beyond their scalar
rank-one shadow, or RH.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace RHB107WeightedGapIncrementFinite

/-- Positive part of a real scalar. -/
def posPart (x : ℝ) : ℝ := max x 0

/-- Scalar negative-eigenvalue depth of a rank-one marked coefficient. -/
def negDepth (x : ℝ) : ℝ := max (-x) 0

@[simp] theorem posPart_nonneg (x : ℝ) : 0 ≤ posPart x := by
  exact le_max_right x 0

/-- Every signed increment is bounded above by its positive part. -/
theorem le_posPart (x : ℝ) : x ≤ posPart x := by
  exact le_max_left x 0

/-- One endpoint step can grow by no more than the positive part of its signed
increment. -/
theorem endpoint_step_upper (x d : ℝ) :
    x + d ≤ x + posPart d := by
  exact add_le_add_left (le_posPart d) x

/-- On a finite family, the signed sum is bounded above by total positive
variation. -/
theorem signed_sum_le_positive_sum
    {ι : Type*} (s : Finset ι) (d : ι → ℝ) :
    (∑ i ∈ s, d i) ≤ ∑ i ∈ s, posPart (d i) := by
  apply Finset.sum_le_sum
  intro i hi
  exact le_posPart (d i)

/-- If every weight on a finite prefix is at least `floor`, the weighted positive
variation controls `floor` times the unweighted positive variation.  This is the
finite core of the monotone-weight prefix estimate used in B107. -/
theorem floor_mul_positive_sum_le_weighted
    {ι : Type*} (s : Finset ι) (ω d : ι → ℝ) (floor : ℝ)
    (hfloor : ∀ i ∈ s, floor ≤ ω i) :
    floor * (∑ i ∈ s, posPart (d i)) ≤
      ∑ i ∈ s, ω i * posPart (d i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right (hfloor i hi) (posPart_nonneg (d i))

/-- Any selector `0 ≤ phi ≤ 1` is dominated by the positive-part selector when
weights are nonnegative. -/
theorem weighted_selector_le_positive_budget
    {ι : Type*} (s : Finset ι) (ω φ d : ι → ℝ)
    (hω : ∀ i ∈ s, 0 ≤ ω i)
    (hφ0 : ∀ i ∈ s, 0 ≤ φ i)
    (hφ1 : ∀ i ∈ s, φ i ≤ 1) :
    (∑ i ∈ s, ω i * φ i * d i) ≤
      ∑ i ∈ s, ω i * posPart (d i) := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases hd : 0 ≤ d i
  · have hgap : 0 ≤ (1 - φ i) * d i :=
      mul_nonneg (sub_nonneg.mpr (hφ1 i hi)) hd
    have hweighted : 0 ≤ ω i * ((1 - φ i) * d i) :=
      mul_nonneg (hω i hi) hgap
    rw [posPart, max_eq_left hd]
    nlinarith
  · have hd' : d i ≤ 0 := le_of_not_ge hd
    have hcoef : 0 ≤ ω i * φ i :=
      mul_nonneg (hω i hi) (hφ0 i hi)
    have hnonpos : (ω i * φ i) * d i ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcoef hd'
    rw [posPart, max_eq_right hd']
    simpa [mul_assoc] using hnonpos

/-- The binary sign selector attains the positive-part budget exactly. -/
def signSelector {ι : Type*} (d : ι → ℝ) (i : ι) : ℝ :=
  if 0 < d i then 1 else 0

@[simp] theorem signSelector_nonneg {ι : Type*} (d : ι → ℝ) (i : ι) :
    0 ≤ signSelector d i := by
  simp [signSelector]

@[simp] theorem signSelector_le_one {ι : Type*} (d : ι → ℝ) (i : ι) :
    signSelector d i ≤ 1 := by
  simp [signSelector]

/-- Exact finite selector attainment: no supremum or compactness argument is
needed. -/
theorem signSelector_attains_positive_budget
    {ι : Type*} (s : Finset ι) (ω d : ι → ℝ) :
    (∑ i ∈ s, ω i * signSelector d i * d i) =
      ∑ i ∈ s, ω i * posPart (d i) := by
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : 0 < d i
  · simp [signSelector, posPart, hd, max_eq_left hd.le]
  · have hd' : d i ≤ 0 := le_of_not_gt hd
    simp [signSelector, posPart, hd, max_eq_right hd']

/-- A scalar perturbation changes positive depth by at most its absolute size in
the one-sided direction needed for the archimedean-correction transfer. -/
theorem posPart_add_le (x e : ℝ) :
    posPart (x + e) ≤ posPart x + |e| := by
  apply max_le
  · exact add_le_add (le_posPart x) (le_abs_self e)
  · exact add_nonneg (posPart_nonneg x) (abs_nonneg e)

/-- Reversing a signed increment turns its positive part into the negative depth
of the corresponding rank-one marked coefficient. -/
@[simp] theorem negDepth_neg (d : ℝ) :
    negDepth (-d) = posPart d := by
  simp [negDepth, posPart]

/-- Exact threshold test for scalar rank-one negative depth: a shifted marked
coefficient is negative precisely below the positive increment depth. -/
theorem shifted_negative_iff_below_increment
    (d y : ℝ) :
    y - d < 0 ↔ y < d := by
  linarith

/-- The basic hostile firewall: perfect signed cancellation can coexist with
strictly positive one-sided mass. -/
theorem cancellation_does_not_kill_positive_mass (a : ℝ) (ha : 0 < a) :
    a + (-a) = 0 ∧ posPart a + posPart (-a) = a := by
  constructor
  · ring
  · rw [posPart, max_eq_left ha.le]
    have hna : -a ≤ 0 := by linarith
    rw [posPart, max_eq_right hna]
    ring

#print axioms posPart_nonneg
#print axioms le_posPart
#print axioms endpoint_step_upper
#print axioms signed_sum_le_positive_sum
#print axioms floor_mul_positive_sum_le_weighted
#print axioms weighted_selector_le_positive_budget
#print axioms signSelector_attains_positive_budget
#print axioms posPart_add_le
#print axioms negDepth_neg
#print axioms shifted_negative_iff_below_increment
#print axioms cancellation_does_not_kill_positive_mass

end RHB107WeightedGapIncrementFinite
