import Mathlib

open scoped BigOperators

namespace RHB123WeightedVarianceHankelPencil

/-!
# RH B123 finite centering / variance / Hankel-pencil core

Finite algebra only.

Formalized here:

* exact centering invariance for a finite zero-mass row;
* the scalar quadratic-cost completion-of-the-square identity and its minimizer;
* the exact determinant of the realified consecutive-Hankel source pencil for
  one nonreal conjugate pair;
* the resulting no-real-root / displacement-blindness firewall;
* the characteristic polynomial of the corresponding real multiplication map;
* the generic conjugation-compatible scalar-filter source block, proving that
  scalar nodewise weighting changes eigenvalue depth but not its one-plus /
  one-minus inertia signature away from exact annihilation.

These are the finite load-bearing identities in the human B123/B123C reduction.
This file does **not** formalize primes, the B46 kernel, PNT error bounds, zeta
zeros, contour integration, Hankel spectral theory, the Riemann hypothesis, or
any Clay conclusion.
-/

/-- A finite signed row of total mass zero is unchanged when every state value is
translated by the same scalar.  This is the exact finite algebra behind B123's
shellwise removal of an arbitrary PNT-state level. -/
theorem zero_mass_centering
    {ι : Type*} (s : Finset ι) (a z : ι → ℝ) (λ : ℝ)
    (hzero : ∑ i ∈ s, a i = 0) :
    (∑ i ∈ s, a i * z i) =
      ∑ i ∈ s, a i * (z i - λ) := by
  calc
    ∑ i ∈ s, a i * (z i - λ)
        = ∑ i ∈ s, (a i * z i - a i * λ) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = (∑ i ∈ s, a i * z i) - (∑ i ∈ s, a i * λ) := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ i ∈ s, a i * z i) - (∑ i ∈ s, a i) * λ := by
          rw [Finset.sum_mul]
    _ = ∑ i ∈ s, a i * z i := by rw [hzero]; ring

/-- Scalar form of a weighted quadratic cost after the finite weights have been
collapsed to total mass `A`, first moment `Z`, and second moment `Q`. -/
def quadraticCost (A Z Q λ : ℝ) : ℝ :=
  Q - 2 * λ * Z + λ ^ 2 * A

/-- Exact completion of the square for the weighted quadratic shell cost. -/
theorem quadratic_cost_complete_square
    (A Z Q λ : ℝ) (hA : A ≠ 0) :
    quadraticCost A Z Q λ =
      quadraticCost A Z Q (Z / A) + A * (λ - Z / A) ^ 2 := by
  unfold quadraticCost
  field_simp [hA]
  ring

/-- For positive total weight, the weighted mean `Z/A` minimizes the quadratic
cost. -/
theorem quadratic_cost_minimized_at_mean
    (A Z Q λ : ℝ) (hA : 0 < A) :
    quadraticCost A Z Q (Z / A) ≤ quadraticCost A Z Q λ := by
  rw [quadratic_cost_complete_square A Z Q λ (ne_of_gt hA)]
  exact le_add_of_nonneg_right (mul_nonneg hA.le (sq_nonneg (λ - Z / A)))

/-- Determinant of the realified source pencil attached to one conjugate pair
`u = a + i b`, after removing one common positive source scale. -/
def pairPencilDet (a b x : ℝ) : ℝ :=
  (a - x) * (-a + x) - b * b

/-- The determinant is the strictly negative sum of two squares. -/
theorem pair_pencil_det_factorization (a b x : ℝ) :
    pairPencilDet a b x = -((a - x) ^ 2 + b ^ 2) := by
  unfold pairPencilDet
  ring

/-- A genuinely nonreal pair has negative determinant for every real shift.
Thus the 2x2 real shifted source pencil has one positive and one negative
source direction for every real shift; its inertia cannot measure `|b|`. -/
theorem pair_pencil_det_negative
    {a b x : ℝ} (hb : b ≠ 0) :
    pairPencilDet a b x < 0 := by
  rw [pair_pencil_det_factorization]
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have ha2 : 0 ≤ (a - x) ^ 2 := sq_nonneg (a - x)
  nlinarith

/-- Consequently the real shifted source pencil has no real generalized root
when the conjugate pair is genuinely nonreal. -/
theorem pair_pencil_has_no_real_root
    {a b x : ℝ} (hb : b ≠ 0) :
    pairPencilDet a b x ≠ 0 := by
  exact ne_of_lt (pair_pencil_det_negative hb)

/-- Characteristic polynomial of the real multiplication matrix
`[[a,-b],[b,a]]`: the complex generalized roots are `a ± i b`, so the
*complex* generalized spectrum retains the displacement which real-shift
inertia loses. -/
theorem pair_multiplication_charpoly_identity (a b t : ℝ) :
    (t - a) * (t - a) - b * (-b) = (t - a) ^ 2 + b ^ 2 := by
  ring

/-- The characteristic polynomial is strictly positive on the real axis for a
nonreal pair. -/
theorem pair_multiplication_charpoly_positive
    {a b t : ℝ} (hb : b ≠ 0) :
    0 < (t - a) ^ 2 + b ^ 2 := by
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have ht2 : 0 ≤ (t - a) ^ 2 := sq_nonneg (t - a)
  nlinarith

/-- Determinant of the generic realified pair source block associated with one
conjugation-compatible scalar node weight `r + i s`. -/
def scalarPairBlockDet (r s : ℝ) : ℝ :=
  r * (-r) - (-s) * (-s)

/-- Every scalar-filter pair block has determinant `-(r²+s²)`. -/
theorem scalar_pair_block_det_factorization (r s : ℝ) :
    scalarPairBlockDet r s = -(r ^ 2 + s ^ 2) := by
  unfold scalarPairBlockDet
  ring

/-- Unless the scalar filter annihilates the node exactly, the pair block has
strictly negative determinant and hence cannot lose its one-plus/one-minus
signature merely because the scalar depth becomes small. -/
theorem scalar_pair_block_det_negative
    {r s : ℝ} (hne : r ≠ 0 ∨ s ≠ 0) :
    scalarPairBlockDet r s < 0 := by
  rw [scalar_pair_block_det_factorization]
  rcases hne with hr | hs
  · have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
    nlinarith
  · have hs2 : 0 < s ^ 2 := sq_pos_of_ne_zero hs
    have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
    nlinarith

/-- Characteristic polynomial identity for the generic scalar-filter source
block `[[r,-s],[-s,-r]]`; the eigenvalue depths are `±sqrt(r²+s²)`. -/
theorem scalar_pair_block_charpoly_identity (r s t : ℝ) :
    (t - r) * (t + r) - s ^ 2 = t ^ 2 - (r ^ 2 + s ^ 2) := by
  ring

#print axioms zero_mass_centering
#print axioms quadratic_cost_complete_square
#print axioms quadratic_cost_minimized_at_mean
#print axioms pair_pencil_det_factorization
#print axioms pair_pencil_det_negative
#print axioms pair_pencil_has_no_real_root
#print axioms pair_multiplication_charpoly_identity
#print axioms pair_multiplication_charpoly_positive
#print axioms scalar_pair_block_det_factorization
#print axioms scalar_pair_block_det_negative
#print axioms scalar_pair_block_charpoly_identity

end RHB123WeightedVarianceHankelPencil
