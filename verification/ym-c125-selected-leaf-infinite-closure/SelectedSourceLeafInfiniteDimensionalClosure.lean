import Mathlib

/-!
# Selected source leaves: dimension-free BKAR/root closure

This file formalizes finite algebra that is valid in arbitrary seminormed
additive spaces and for arbitrarily large finite tree vertex sets.

The intended application is the fixed-placement source-leaf extension of a
replica--BKAR tree estimate.  If each selected source leaf contributes a fixed
local rate while leaving the covariance-edge derivative currency unchanged,
then the product over all vertices factors into

* the original bulk/tree product; and
* one root-rate factor for each selected leaf.

For at most two selected leaves, this changes only a fixed prefactor.  It does
not change the strict nonroot branch threshold.  A separate normed-space
zero/one/two-root theorem then absorbs the resulting lower-triangular rooted
hierarchy with the same denominator `1 - branch`.

The file does not formalize the replica--BKAR identity, Kirk's activity
spaces, Gaussian integration, source atoms, localization, renormalization,
Schwinger functions, Yang--Mills theory, a mass gap, or a Clay theorem.
-/

open scoped BigOperators

namespace Millennium.YangMills.SelectedSourceLeafInfiniteDimensionalClosure

/-- Products of vertexwise powers of one common root rate collect into the
power of the total selected-leaf count. -/
theorem finset_prod_pow_eq_pow_sum
    {ι : Type*} (s : Finset ι) (rootRate : ℝ) (rootCount : ι → ℕ) :
    (∏ i ∈ s, rootRate ^ rootCount i) =
      rootRate ^ (∑ i ∈ s, rootCount i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih, pow_add]

/-- Exact factorization of a fixed selected-leaf placement over an arbitrary
finite vertex set.  The edge factor is untouched. -/
theorem selected_leaf_product_factorization
    {ι : Type*} (s : Finset ι)
    (bulk edge : ι → ℝ) (rootCount : ι → ℕ) (rootRate : ℝ) :
    (∏ i ∈ s, bulk i * rootRate ^ rootCount i * edge i) =
      (∏ i ∈ s, bulk i) *
        rootRate ^ (∑ i ∈ s, rootCount i) *
          (∏ i ∈ s, edge i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih, pow_add]
      ring

/-- A pointwise fixed-placement estimate multiplies over the complete tree.
No dimension, degree, or number-of-vertices constant is introduced beyond the
explicit products already present. -/
theorem selected_leaf_product_bound
    {ι : Type*} (s : Finset ι)
    (atom bulk edge : ι → ℝ) (rootCount : ι → ℕ) (rootRate : ℝ)
    (hatom0 : ∀ i ∈ s, 0 ≤ atom i)
    (hpoint : ∀ i ∈ s,
      atom i ≤ bulk i * rootRate ^ rootCount i * edge i) :
    (∏ i ∈ s, atom i) ≤
      (∏ i ∈ s, bulk i) *
        rootRate ^ (∑ i ∈ s, rootCount i) *
          (∏ i ∈ s, edge i) := by
  classical
  calc
    (∏ i ∈ s, atom i) ≤
        ∏ i ∈ s, bulk i * rootRate ^ rootCount i * edge i := by
      exact Finset.prod_le_prod hatom0 hpoint
    _ =
        (∏ i ∈ s, bulk i) *
          rootRate ^ (∑ i ∈ s, rootCount i) *
            (∏ i ∈ s, edge i) :=
      selected_leaf_product_factorization s bulk edge rootCount rootRate

/-- A nonnegative root rate raised to at most two selected leaves is bounded
by one fixed square prefactor. -/
theorem at_most_two_root_rate_bound
    (rootRate : ℝ) (q : ℕ) (hrootRate : 0 ≤ rootRate) (hq : q ≤ 2) :
    rootRate ^ q ≤ (max 1 rootRate) ^ 2 := by
  have hM1 : 1 ≤ max 1 rootRate := le_max_left 1 rootRate
  have hRM : rootRate ≤ max 1 rootRate := le_max_right 1 rootRate
  have hM0 : 0 ≤ max 1 rootRate := le_trans (by norm_num) hM1
  rcases (show q = 0 ∨ q = 1 ∨ q = 2 by omega) with rfl | rfl | rfl
  · have hmul : 0 ≤ (max 1 rootRate - 1) * (max 1 rootRate + 1) :=
      mul_nonneg (sub_nonneg.mpr hM1) (add_nonneg hM0 (by norm_num))
    norm_num [pow_two]
    nlinarith
  · have hmul : 0 ≤
        (max 1 rootRate) * (max 1 rootRate - 1) :=
      mul_nonneg hM0 (sub_nonneg.mpr hM1)
    simp only [pow_one]
    nlinarith
  · have hmul : 0 ≤
        (max 1 rootRate - rootRate) *
          (max 1 rootRate + rootRate) :=
      mul_nonneg (sub_nonneg.mpr hRM) (add_nonneg hM0 hrootRate)
    nlinarith [hmul]

/-- Complete fixed-placement estimate for at most two selected source leaves.
The root layer changes only the fixed prefactor `(max 1 rootRate)^2`; the
original bulk and edge products are preserved. -/
theorem at_most_two_selected_leaves_preserve_tree_currency
    {ι : Type*} (s : Finset ι)
    (atom bulk edge : ι → ℝ) (rootCount : ι → ℕ) (rootRate : ℝ)
    (hatom0 : ∀ i ∈ s, 0 ≤ atom i)
    (hbulk0 : ∀ i ∈ s, 0 ≤ bulk i)
    (hedge0 : ∀ i ∈ s, 0 ≤ edge i)
    (hrootRate : 0 ≤ rootRate)
    (hpoint : ∀ i ∈ s,
      atom i ≤ bulk i * rootRate ^ rootCount i * edge i)
    (hrootCount : (∑ i ∈ s, rootCount i) ≤ 2) :
    (∏ i ∈ s, atom i) ≤
      (max 1 rootRate) ^ 2 *
        (∏ i ∈ s, bulk i) *
          (∏ i ∈ s, edge i) := by
  classical
  have htree := selected_leaf_product_bound
    s atom bulk edge rootCount rootRate hatom0 hpoint
  have hroot := at_most_two_root_rate_bound
    rootRate (∑ i ∈ s, rootCount i) hrootRate hrootCount
  have hbulkProd : 0 ≤ ∏ i ∈ s, bulk i := by
    exact Finset.prod_nonneg hbulk0
  have hedgeProd : 0 ≤ ∏ i ∈ s, edge i := by
    exact Finset.prod_nonneg hedge0
  have hcurrency :
      0 ≤ (∏ i ∈ s, bulk i) * (∏ i ∈ s, edge i) :=
    mul_nonneg hbulkProd hedgeProd
  have hscaled := mul_le_mul_of_nonneg_right hroot hcurrency
  calc
    (∏ i ∈ s, atom i) ≤
        (∏ i ∈ s, bulk i) *
          rootRate ^ (∑ i ∈ s, rootCount i) *
            (∏ i ∈ s, edge i) := htree
    _ = rootRate ^ (∑ i ∈ s, rootCount i) *
        ((∏ i ∈ s, bulk i) * (∏ i ∈ s, edge i)) := by ring
    _ ≤ (max 1 rootRate) ^ 2 *
        ((∏ i ∈ s, bulk i) * (∏ i ∈ s, edge i)) := hscaled
    _ = (max 1 rootRate) ^ 2 *
        (∏ i ∈ s, bulk i) * (∏ i ∈ s, edge i) := by ring

/-- Scalar absorption used by the arbitrary-seminormed-space theorem below. -/
theorem absorb_strict_norm_recursion
    (root total branch : ℝ)
    (hbranch : branch < 1)
    (hrec : total ≤ root + branch * total) :
    total ≤ root / (1 - branch) := by
  have hden : 0 < 1 - branch := sub_pos.mpr hbranch
  apply (le_div_iff₀ hden).2
  nlinarith

/--
Dimension-free zero/one/two-root absorption.

The three states may live in unrelated arbitrary seminormed additive spaces.
Only their norm recurrences are used.  The same strict nonroot branch factor
controls every root level; finite cross-root couplings change prefactors but
create no new smallness threshold.
-/
theorem zero_one_two_root_seminormed_absorption
    {E0 E1 E2 : Type*}
    [SeminormedAddCommGroup E0]
    [SeminormedAddCommGroup E1]
    [SeminormedAddCommGroup E2]
    (root0 total0 : E0) (root1 total1 : E1) (root2 total2 : E2)
    (branch c10 c20 c21 : ℝ)
    (hbranch : branch < 1)
    (hc10 : 0 ≤ c10) (hc20 : 0 ≤ c20) (hc21 : 0 ≤ c21)
    (h0 : ‖total0‖ ≤ ‖root0‖ + branch * ‖total0‖)
    (h1 : ‖total1‖ ≤
      ‖root1‖ + branch * ‖total1‖ + c10 * ‖total0‖)
    (h2 : ‖total2‖ ≤
      ‖root2‖ + branch * ‖total2‖ +
        c21 * ‖total1‖ + c20 * ‖total0‖) :
    ‖total0‖ ≤ ‖root0‖ / (1 - branch) ∧
      ‖total1‖ ≤
        (‖root1‖ + c10 * (‖root0‖ / (1 - branch))) /
          (1 - branch) ∧
      ‖total2‖ ≤
        (‖root2‖ +
            c21 *
              ((‖root1‖ + c10 * (‖root0‖ / (1 - branch))) /
                (1 - branch)) +
            c20 * (‖root0‖ / (1 - branch))) /
          (1 - branch) := by
  have h0bound : ‖total0‖ ≤ ‖root0‖ / (1 - branch) :=
    absorb_strict_norm_recursion
      ‖root0‖ ‖total0‖ branch hbranch h0
  have hc10bound :
      c10 * ‖total0‖ ≤ c10 * (‖root0‖ / (1 - branch)) :=
    mul_le_mul_of_nonneg_left h0bound hc10
  have hrec1 :
      ‖total1‖ ≤
        (‖root1‖ + c10 * (‖root0‖ / (1 - branch))) +
          branch * ‖total1‖ := by
    calc
      ‖total1‖ ≤
          ‖root1‖ + branch * ‖total1‖ + c10 * ‖total0‖ := h1
      _ ≤ ‖root1‖ + branch * ‖total1‖ +
          c10 * (‖root0‖ / (1 - branch)) := by
        linarith
      _ = (‖root1‖ + c10 * (‖root0‖ / (1 - branch))) +
          branch * ‖total1‖ := by ring
  have h1bound :
      ‖total1‖ ≤
        (‖root1‖ + c10 * (‖root0‖ / (1 - branch))) /
          (1 - branch) :=
    absorb_strict_norm_recursion
      (‖root1‖ + c10 * (‖root0‖ / (1 - branch)))
      ‖total1‖ branch hbranch hrec1
  have hc21bound :
      c21 * ‖total1‖ ≤
        c21 *
          ((‖root1‖ + c10 * (‖root0‖ / (1 - branch))) /
            (1 - branch)) :=
    mul_le_mul_of_nonneg_left h1bound hc21
  have hc20bound :
      c20 * ‖total0‖ ≤ c20 * (‖root0‖ / (1 - branch)) :=
    mul_le_mul_of_nonneg_left h0bound hc20
  have hrec2 :
      ‖total2‖ ≤
        (‖root2‖ +
            c21 *
              ((‖root1‖ + c10 * (‖root0‖ / (1 - branch))) /
                (1 - branch)) +
            c20 * (‖root0‖ / (1 - branch))) +
          branch * ‖total2‖ := by
    calc
      ‖total2‖ ≤
          ‖root2‖ + branch * ‖total2‖ +
            c21 * ‖total1‖ + c20 * ‖total0‖ := h2
      _ ≤ ‖root2‖ + branch * ‖total2‖ +
          c21 *
            ((‖root1‖ + c10 * (‖root0‖ / (1 - branch))) /
              (1 - branch)) +
          c20 * (‖root0‖ / (1 - branch)) := by
        linarith
      _ =
          (‖root2‖ +
              c21 *
                ((‖root1‖ + c10 * (‖root0‖ / (1 - branch))) /
                  (1 - branch)) +
              c20 * (‖root0‖ / (1 - branch))) +
            branch * ‖total2‖ := by ring
  have h2bound :
      ‖total2‖ ≤
        (‖root2‖ +
            c21 *
              ((‖root1‖ + c10 * (‖root0‖ / (1 - branch))) /
                (1 - branch)) +
            c20 * (‖root0‖ / (1 - branch))) /
          (1 - branch) :=
    absorb_strict_norm_recursion
      (‖root2‖ +
        c21 *
          ((‖root1‖ + c10 * (‖root0‖ / (1 - branch))) /
            (1 - branch)) +
        c20 * (‖root0‖ / (1 - branch)))
      ‖total2‖ branch hbranch hrec2
  exact ⟨h0bound, h1bound, h2bound⟩

/-- Multiplying a connected/cumulant factorial envelope by a partition-count
envelope adds one finite factorial-growth exponent.  This is the scalar shell
behind replacing an ordinary source disk by the weaker finite-factorial-growth
condition used in the Osterwalder--Schrader reconstruction theorem. -/
theorem cumulant_partition_to_moment_factorial_growth
    (n p : ℕ)
    (connected partitionMass moment A B R S : ℝ)
    (hconnected0 : 0 ≤ connected)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hconnected :
      connected ≤ A * (n.factorial : ℝ) ^ p * R ^ n)
    (hpartition :
      partitionMass ≤ B * (n.factorial : ℝ) * S ^ n)
    (hmoment : moment ≤ partitionMass * connected) :
    moment ≤
      A * B * (n.factorial : ℝ) ^ (p + 1) * (R * S) ^ n := by
  have hconnectedUpper :
      0 ≤ A * (n.factorial : ℝ) ^ p * R ^ n := by
    positivity
  have hproduct :
      partitionMass * connected ≤
        (B * (n.factorial : ℝ) * S ^ n) *
          (A * (n.factorial : ℝ) ^ p * R ^ n) :=
    mul_le_mul hpartition hconnected hconnected0 (by positivity)
  calc
    moment ≤ partitionMass * connected := hmoment
    _ ≤
        (B * (n.factorial : ℝ) * S ^ n) *
          (A * (n.factorial : ℝ) ^ p * R ^ n) := hproduct
    _ = A * B * (n.factorial : ℝ) ^ (p + 1) * (R * S) ^ n := by
      rw [pow_add, mul_pow]
      ring

#print axioms finset_prod_pow_eq_pow_sum
#print axioms selected_leaf_product_factorization
#print axioms selected_leaf_product_bound
#print axioms at_most_two_root_rate_bound
#print axioms at_most_two_selected_leaves_preserve_tree_currency
#print axioms absorb_strict_norm_recursion
#print axioms zero_one_two_root_seminormed_absorption
#print axioms cumulant_partition_to_moment_factorial_growth

end Millennium.YangMills.SelectedSourceLeafInfiniteDimensionalClosure
