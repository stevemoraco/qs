import Mathlib

/-!
# Yu asymmetric direction weights and projective covariance

Finite real algebra only.

The intended analytic application is to a symmetric projective direction defect
weighted asymmetrically by two nonnegative amplitudes.  Symmetrizing the ordered
pair integral produces the geometric-mean weight, and the resulting pairwise
projective energy controls the distance of the direction covariance from a
rank-one projector.

This file does **not** formalize Runlong Yu's PDE estimates, integration,
matrix-valued measures, eigenvalue existence for covariance operators,
compactness, Navier--Stokes regularity, or blow-up.
-/

namespace NSYuAsymmetricProjectiveCovariance

/-- Exact scalar identity behind symmetrization of the asymmetric cubic weight. -/
theorem cubic_pair_gap_identity (r s : ℝ) :
    r ^ 4 * s ^ 2 + r ^ 2 * s ^ 4 - 2 * (r ^ 3 * s ^ 3) =
      r ^ 2 * s ^ 2 * (r - s) ^ 2 := by
  ring

/-- The geometric-mean cubic weight is dominated by the average of the two
ordered asymmetric weights.  No sign assumption is needed on `r,s`; only the
defect multiplier must be nonnegative. -/
theorem cubic_pair_symmetrization
    (r s d : ℝ) (hd : 0 ≤ d) :
    2 * (r ^ 3 * s ^ 3 * d) ≤
      (r ^ 4 * s ^ 2 + r ^ 2 * s ^ 4) * d := by
  have hgap :
      0 ≤ r ^ 4 * s ^ 2 + r ^ 2 * s ^ 4 -
        2 * (r ^ 3 * s ^ 3) := by
    rw [cubic_pair_gap_identity]
    positivity
  have hbase :
      2 * (r ^ 3 * s ^ 3) ≤
        r ^ 4 * s ^ 2 + r ^ 2 * s ^ 4 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hbase hd
  calc
    2 * (r ^ 3 * s ^ 3 * d) = (2 * (r ^ 3 * s ^ 3)) * d := by ring
    _ ≤ (r ^ 4 * s ^ 2 + r ^ 2 * s ^ 4) * d := hmul

/-- Once the forward and reverse ordered energies agree, the pointwise
symmetrization inequality controls the symmetric energy by either ordered one. -/
theorem equal_reverse_energies_control_symmetric
    (forward reverse symmetric : ℝ)
    (hpoint : 2 * symmetric ≤ forward + reverse)
    (hswap : reverse = forward) :
    symmetric ≤ forward := by
  linarith

/-- A nonnegative eigenvalue below the top eigenvalue has its square controlled
by the top eigenvalue times itself. -/
theorem square_le_top_mul
    (top x : ℝ) (hx : 0 ≤ x) (hxt : x ≤ top) :
    x ^ 2 ≤ top * x := by
  nlinarith

/-- For a nonnegative trace-one spectrum, the squared trace is at most the top
eigenvalue. -/
theorem trace_square_le_top
    (l1 l2 l3 : ℝ)
    (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) (h3 : 0 ≤ l3)
    (h21 : l2 ≤ l1) (h31 : l3 ≤ l1)
    (htrace : l1 + l2 + l3 = 1) :
    l1 ^ 2 + l2 ^ 2 + l3 ^ 2 ≤ l1 := by
  have h11 := square_le_top_mul l1 l1 h1 (le_refl l1)
  have h22 := square_le_top_mul l1 l2 h2 h21
  have h33 := square_le_top_mul l1 l3 h3 h31
  nlinarith

/-- The mass transverse to the top eigendirection is bounded by the covariance
impurity `1 - tr(P^2)`. -/
theorem top_residual_le_impurity
    (l1 l2 l3 : ℝ)
    (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) (h3 : 0 ≤ l3)
    (h21 : l2 ≤ l1) (h31 : l3 ≤ l1)
    (htrace : l1 + l2 + l3 = 1) :
    1 - l1 ≤ 1 - (l1 ^ 2 + l2 ^ 2 + l3 ^ 2) := by
  have hs := trace_square_le_top l1 l2 l3 h1 h2 h3 h21 h31 htrace
  linarith

/-- The covariance impurity is nonnegative for every nonnegative trace-one
three-point spectrum. -/
theorem spectral_impurity_nonneg
    (l1 l2 l3 : ℝ)
    (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) (h3 : 0 ≤ l3)
    (h21 : l2 ≤ l1) (h31 : l3 ≤ l1)
    (htrace : l1 + l2 + l3 = 1) :
    0 ≤ 1 - (l1 ^ 2 + l2 ^ 2 + l3 ^ 2) := by
  have hs := trace_square_le_top l1 l2 l3 h1 h2 h3 h21 h31 htrace
  have hl1 : l1 ≤ 1 := by linarith
  linarith

/-- A quantitative impurity bound forces concentration onto the top
projective direction. -/
theorem impurity_bound_forces_top_concentration
    (l1 l2 l3 eps : ℝ)
    (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) (h3 : 0 ≤ l3)
    (h21 : l2 ≤ l1) (h31 : l3 ≤ l1)
    (htrace : l1 + l2 + l3 = 1)
    (himp :
      1 - (l1 ^ 2 + l2 ^ 2 + l3 ^ 2) ≤ eps) :
    1 - l1 ≤ eps := by
  have hres :=
    top_residual_le_impurity l1 l2 l3 h1 h2 h3 h21 h31 htrace
  linarith

/-- The second eigenvalue is controlled by the same impurity currency. -/
theorem second_eigenvalue_le_impurity
    (l1 l2 l3 : ℝ)
    (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) (h3 : 0 ≤ l3)
    (h21 : l2 ≤ l1) (h31 : l3 ≤ l1)
    (htrace : l1 + l2 + l3 = 1) :
    l2 ≤ 1 - (l1 ^ 2 + l2 ^ 2 + l3 ^ 2) := by
  have hres :=
    top_residual_le_impurity l1 l2 l3 h1 h2 h3 h21 h31 htrace
  nlinarith

/-- In eigenvalue coordinates, the squared Frobenius distance from the top
rank-one projector is no larger than the impurity. -/
theorem rankOne_distance_le_impurity
    (l1 l2 l3 : ℝ)
    (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) (h3 : 0 ≤ l3)
    (h21 : l2 ≤ l1) (h31 : l3 ≤ l1)
    (htrace : l1 + l2 + l3 = 1) :
    (1 - l1) ^ 2 + l2 ^ 2 + l3 ^ 2 ≤
      1 - (l1 ^ 2 + l2 ^ 2 + l3 ^ 2) := by
  have hs := trace_square_le_top l1 l2 l3 h1 h2 h3 h21 h31 htrace
  nlinarith

/-- Zero impurity forces the trace-one spectrum to be exactly rank one. -/
theorem zero_impurity_forces_rank_one
    (l1 l2 l3 : ℝ)
    (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) (h3 : 0 ≤ l3)
    (h21 : l2 ≤ l1) (h31 : l3 ≤ l1)
    (htrace : l1 + l2 + l3 = 1)
    (hzero :
      1 - (l1 ^ 2 + l2 ^ 2 + l3 ^ 2) = 0) :
    l1 = 1 ∧ l2 = 0 ∧ l3 = 0 := by
  have hres :=
    top_residual_le_impurity l1 l2 l3 h1 h2 h3 h21 h31 htrace
  have hl1le : l1 ≤ 1 := by linarith
  have hl1 : l1 = 1 := by linarith
  constructor
  · exact hl1
  constructor <;> nlinarith

#print axioms cubic_pair_gap_identity
#print axioms cubic_pair_symmetrization
#print axioms equal_reverse_energies_control_symmetric
#print axioms square_le_top_mul
#print axioms trace_square_le_top
#print axioms top_residual_le_impurity
#print axioms spectral_impurity_nonneg
#print axioms impurity_bound_forces_top_concentration
#print axioms second_eigenvalue_le_impurity
#print axioms rankOne_distance_le_impurity
#print axioms zero_impurity_forces_rank_one

end NSYuAsymmetricProjectiveCovariance
