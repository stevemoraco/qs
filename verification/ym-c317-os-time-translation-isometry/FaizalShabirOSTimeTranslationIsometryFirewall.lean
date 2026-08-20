import Mathlib

/-!
# Faizal–Shabir OS time-translation isometry firewall

Finite real algebra only.  This file records the scalar spectral shadow of a
source-level issue in the continuum OS reconstruction: positive-time
translations in a nontrivial positive-energy OS semigroup are contractions,
not norm-preserving isometries on every excited vector.

The intended source correction is the standard reflected two-time identity

  ||[tau_t F]||_OS^2 = <[F], U(2t)[F]>,

not equality with ||[F]||_OS^2.

This file does not formalize Osterwalder--Schrader reconstruction, Yang--Mills,
reflection positivity, a continuum Hamiltonian, a mass gap, AF/IR
identification, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirOSTimeTranslationIsometryFirewall

/-- A concrete nontrivial contraction already contradicts norm preservation. -/
theorem half_step_is_not_isometric :
    (((1 / 2 : ℝ) * 1) ^ 2) ≠ (1 : ℝ) ^ 2 := by
  norm_num

/-- A nonnegative scalar spectral multiplier with unit squared norm must equal
one.  This is the finite spectral shadow of: a positive self-adjoint isometry
has no strictly contracting spectral values. -/
theorem nonnegative_isometric_multiplier_eq_one
    (q : ℝ) (hq : 0 ≤ q) (hiso : q ^ 2 = 1) :
    q = 1 := by
  nlinarith [sq_nonneg (q - 1)]

/-- Consequently a nonnegative strict contraction cannot satisfy the source's
norm-preserving identity. -/
theorem strict_contraction_not_isometric
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    q ^ 2 ≠ 1 := by
  intro hiso
  have hqeq : q = 1 :=
    nonnegative_isometric_multiplier_eq_one q hq0 hiso
  linarith

/-- Scalar semigroup shadow of the correct OS two-time norm formula: shifting
by one positive-time step with multiplier `q` squares the multiplier in the
squared norm, exactly as a `2t` matrix element does. -/
theorem shifted_norm_equals_double_time_matrix_element
    (q x : ℝ) :
    (q * x) ^ 2 = x * (q ^ 2 * x) := by
  ring

/-- If a positive spectral multiplier is strictly below one and the vector is
nonzero, the squared norm at one step cannot equal the original squared norm.
The statement is kept in multiplicative form to mirror a one-dimensional
spectral subspace. -/
theorem positive_excited_multiplier_loses_norm
    (q x : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hx : x ≠ 0) :
    (q * x) ^ 2 < x ^ 2 := by
  have hq2 : q ^ 2 < 1 := by
    nlinarith [sq_nonneg (q + 1)]
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  calc
    (q * x) ^ 2 = q ^ 2 * x ^ 2 := by ring
    _ < 1 * x ^ 2 := by
      exact mul_lt_mul_of_pos_right hq2 hx2
    _ = x ^ 2 := by ring

#print axioms half_step_is_not_isometric
#print axioms nonnegative_isometric_multiplier_eq_one
#print axioms strict_contraction_not_isometric
#print axioms shifted_norm_equals_double_time_matrix_element
#print axioms positive_excited_multiplier_loses_norm

end Millennium.YangMills.FaizalShabirOSTimeTranslationIsometryFirewall
