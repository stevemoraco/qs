import Mathlib

namespace RHB124CoarseVarianceCommutatorMetric

/-!
# RH B124 finite coarse-scale / commutator core

Finite real and rational algebra only.

The human B124 reduction has two new load-bearing finite pieces:

1. the physical coarse-graining exponent `H = X^(1-1/(2p))` is exactly the
   scale at which the generic within-block path-energy power vanishes;
2. on one realified nonreal conjugate-pair source plane, the commutator of the
   signature form and the first coordinate-moment form has square `-4 b^2 I`,
   so a shifted scalar detector changes sign exactly when `|b|` crosses the
   prescribed displacement threshold.

This file deliberately does **not** formalize primes, PNT error estimates,
weighted Jensen/Cauchy over prime shells, zeta/Xi zeros, contour integrals,
Hankel matrix inertia, Gram whitening, the Riemann hypothesis, or any Clay
conclusion.
-/

/-- The scalar diagonal entry of the squared source commutator
`[[0,-2b],[2b,0]]^2`. -/
def commutatorSquareScalar (b : ℝ) : ℝ := -4 * b ^ 2

/-- The two diagonal products in the squared source commutator are both
`-4 b^2`. -/
theorem source_commutator_square_diagonal (b : ℝ) :
    (-2 * b) * (2 * b) = -4 * b ^ 2 ∧
      (2 * b) * (-2 * b) = -4 * b ^ 2 := by
  constructor <;> ring

/-- The Euclidean squared-column size of either nonzero commutator column is
`4 b^2`. -/
theorem source_commutator_energy_diagonal (b : ℝ) :
    (2 * b) ^ 2 = 4 * b ^ 2 ∧ (-2 * b) ^ 2 = 4 * b ^ 2 := by
  constructor <;> ring

/-- Scalar shifted detector corresponding to
`4 delta^2 I + [J,K]^2` on one pair plane. -/
def displacementDetector (delta b : ℝ) : ℝ :=
  4 * delta ^ 2 + commutatorSquareScalar b

/-- Exact factorization of the shifted detector. -/
theorem displacement_detector_factorization (delta b : ℝ) :
    displacementDetector delta b = 4 * (delta ^ 2 - b ^ 2) := by
  unfold displacementDetector commutatorSquareScalar
  ring

/-- If `b` lies in the real band `[-delta,delta]`, the shifted detector is
nonnegative. -/
theorem displacement_detector_nonneg_of_band
    {delta b : ℝ} (hdelta : 0 ≤ delta)
    (hlo : -delta ≤ b) (hhi : b ≤ delta) :
    0 ≤ displacementDetector delta b := by
  rw [displacement_detector_factorization]
  have hleft : 0 ≤ delta - b := sub_nonneg.mpr hhi
  have hright : 0 ≤ delta + b := by linarith
  have hprod : 0 ≤ (delta - b) * (delta + b) :=
    mul_nonneg hleft hright
  nlinarith

/-- Crossing above the positive displacement threshold makes the detector
strictly negative. -/
theorem displacement_detector_negative_of_above
    {delta b : ℝ} (hdelta : 0 ≤ delta) (habove : delta < b) :
    displacementDetector delta b < 0 := by
  rw [displacement_detector_factorization]
  have h1 : 0 < b - delta := sub_pos.mpr habove
  have h2 : 0 < b + delta := by linarith
  have hprod : 0 < (b - delta) * (b + delta) := mul_pos h1 h2
  nlinarith

/-- Crossing below the negative displacement threshold also makes the detector
strictly negative. -/
theorem displacement_detector_negative_of_below
    {delta b : ℝ} (hdelta : 0 ≤ delta) (hbelow : b < -delta) :
    displacementDetector delta b < 0 := by
  rw [displacement_detector_factorization]
  have h1 : b - delta < 0 := by linarith
  have h2 : b + delta < 0 := by linarith
  have hprod : 0 < (b - delta) * (b + delta) :=
    mul_pos_of_neg_of_neg h1 h2
  nlinarith

/-- Exact two-block weighted between-variance identity.  This is the scalar
shadow of the ANOVA decomposition used in the coarse PNT-state reduction. -/
def weightedMean2 (A B x y : ℝ) : ℝ :=
  (A * x + B * y) / (A + B)

theorem two_block_between_variance_identity
    (A B x y : ℝ) (hAB : A + B ≠ 0) :
    A * (x - weightedMean2 A B x y) ^ 2 +
        B * (y - weightedMean2 A B x y) ^ 2 =
      (A * B / (A + B)) * (x - y) ^ 2 := by
  unfold weightedMean2
  field_simp [hAB]
  ring

/-- The exponent in the generic B124 within-block bound vanishes exactly at
`H = X^(1-1/(2p))`. -/
theorem critical_coarse_exponent
    {p : ℝ} (hp : p ≠ 0) :
    p * (1 - 1 / (2 * p)) + 1 / 2 - p = 0 := by
  field_simp [hp]
  ring

/-- Moving the coarse scale exponent upward by `delta` leaves exactly the fixed
power `p*delta`. -/
theorem supercritical_coarse_exponent_identity
    {p delta : ℝ} (hp : p ≠ 0) :
    p * (1 - 1 / (2 * p) + delta) + 1 / 2 - p = p * delta := by
  field_simp [hp]
  ring

/-- For positive `p` and positive scale overshoot, the leftover exponent is
strictly positive. -/
theorem supercritical_coarse_exponent_positive
    {p delta : ℝ} (hp : 0 < p) (hdelta : 0 < delta) :
    0 < p * (1 - 1 / (2 * p) + delta) + 1 / 2 - p := by
  rw [supercritical_coarse_exponent_identity (ne_of_gt hp)]
  exact mul_pos hp hdelta

/-- The first strip rung `p=2` has the critical physical exponent `3/4`. -/
theorem quadratic_rung_critical_exponent :
    (2 : ℚ) * (3 / 4) + 1 / 2 - 2 = 0 := by
  norm_num

/-- In `q`-notation, `p=q/(q-1)` gives the critical physical exponent
`1/2+1/(2q)`. -/
theorem conjugate_exponent_critical_scale
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    1 - 1 / (2 * (q / (q - 1))) = 1 / 2 + 1 / (2 * q) := by
  field_simp [hq0, hq1]
  ring

#print axioms commutatorSquareScalar
#print axioms source_commutator_square_diagonal
#print axioms source_commutator_energy_diagonal
#print axioms displacementDetector
#print axioms displacement_detector_factorization
#print axioms displacement_detector_nonneg_of_band
#print axioms displacement_detector_negative_of_above
#print axioms displacement_detector_negative_of_below
#print axioms weightedMean2
#print axioms two_block_between_variance_identity
#print axioms critical_coarse_exponent
#print axioms supercritical_coarse_exponent_identity
#print axioms supercritical_coarse_exponent_positive
#print axioms quadratic_rung_critical_exponent
#print axioms conjugate_exponent_critical_scale

end RHB124CoarseVarianceCommutatorMetric
