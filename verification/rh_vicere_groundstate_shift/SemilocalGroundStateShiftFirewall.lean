import Mathlib

/-!
# Semilocal ground-state shift firewall

Finite algebra behind an audit of a claimed semilocal-spectral proof of RH.

A self-adjoint construction built from a shifted quadratic form

  `qShifted = qRaw - ε * normSq`

may have real spectrum and a nonnegative shifted form even when the original
form is negative.  To recover nonnegativity of the original form one must pay
the sign `0 ≤ ε`; if `ε < 0` and the shifted form has a null ground vector,
the original form is strictly negative on that vector.

No zeta function, Weil form, semilocal operator, spectral determinant, or RH
statement is formalized here.
-/

namespace Millennium.RH.SemilocalGroundStateShiftFirewall

/-- Reconstruct the unshifted quadratic value from the shifted value and the
ground-state shift. -/
def rawFromShift (shifted ε normSq : ℝ) : ℝ :=
  shifted + ε * normSq

/-- A nonnegative shifted value and a nonnegative ground-state shift imply a
nonnegative unshifted value.  The sign of `ε` is load-bearing. -/
theorem raw_nonnegative_of_shifted_and_ground_nonnegative
    (shifted ε normSq : ℝ)
    (hshifted : 0 ≤ shifted)
    (hε : 0 ≤ ε)
    (hnorm : 0 ≤ normSq) :
    0 ≤ rawFromShift shifted ε normSq := by
  dsimp [rawFromShift]
  positivity

/-- If the ground-state shift is negative and a positive-norm ground vector is
null for the shifted form, the original form is strictly negative there. -/
theorem raw_negative_at_shifted_null_of_negative_ground
    (ε normSq : ℝ)
    (hε : ε < 0)
    (hnorm : 0 < normSq) :
    rawFromShift 0 ε normSq < 0 := by
  dsimp [rawFromShift]
  exact mul_neg_of_neg_of_pos hε hnorm

/-- The source-shaped eigenvector statement: `q = ε * ||v||²` with negative
`ε` and nonzero `v` is a strict negative direction of the original form. -/
theorem negative_raw_ground_direction
    (q ε normSq : ℝ)
    (hground : q = ε * normSq)
    (hε : ε < 0)
    (hnorm : 0 < normSq) :
    q < 0 := by
  rw [hground]
  exact mul_neg_of_neg_of_pos hε hnorm

/-- Concrete two-dimensional raw indefinite quadratic form. -/
def qRaw (x y : ℝ) : ℝ :=
  -(x ^ 2) + y ^ 2

/-- Shift by the smallest eigenvalue `-1`: `qRaw - (-1)||·||²`. -/
def qShifted (x y : ℝ) : ℝ :=
  qRaw x y + (x ^ 2 + y ^ 2)

/-- The shifted form is globally nonnegative. -/
theorem shifted_form_nonnegative (x y : ℝ) :
    0 ≤ qShifted x y := by
  dsimp [qShifted, qRaw]
  nlinarith [sq_nonneg y]

/-- The original form has a strict negative ground direction. -/
theorem raw_form_negative_ground :
    qRaw 1 0 < 0 := by
  norm_num [qRaw]

/-- The shifted ground vector is null. -/
theorem shifted_ground_is_null :
    qShifted 1 0 = 0 := by
  norm_num [qShifted, qRaw]

/-- Exact counterexample: global nonnegativity of the shifted form does not
imply global nonnegativity of the original form. -/
theorem shifted_psd_does_not_imply_raw_psd :
    (∀ x y : ℝ, 0 ≤ qShifted x y) ∧
      ¬ (∀ x y : ℝ, 0 ≤ qRaw x y) := by
  constructor
  · exact shifted_form_nonnegative
  · intro h
    have h10 := h 1 0
    linarith [raw_form_negative_ground]

/-- Even a shifted sum-of-squares identity at every point is compatible with a
negative original form when the ground shift is negative. -/
theorem sum_of_squares_shift_firewall :
    (∀ x y : ℝ, qShifted x y = 2 * y ^ 2) ∧
      qRaw 1 0 = -1 := by
  constructor
  · intro x y
    dsimp [qShifted, qRaw]
    ring
  · norm_num [qRaw]

/-- The precise repair disjunction at a shifted null vector: if the original
value is nonnegative there and the norm is positive, the shift cannot be
negative. -/
theorem original_nonnegative_forces_ground_nonnegative
    (ε normSq : ℝ)
    (hnorm : 0 < normSq)
    (hraw : 0 ≤ rawFromShift 0 ε normSq) :
    0 ≤ ε := by
  dsimp [rawFromShift] at hraw
  exact nonneg_of_mul_nonneg_left hraw (le_of_lt hnorm)

#print axioms raw_nonnegative_of_shifted_and_ground_nonnegative
#print axioms raw_negative_at_shifted_null_of_negative_ground
#print axioms negative_raw_ground_direction
#print axioms shifted_form_nonnegative
#print axioms raw_form_negative_ground
#print axioms shifted_ground_is_null
#print axioms shifted_psd_does_not_imply_raw_psd
#print axioms sum_of_squares_shift_firewall
#print axioms original_nonnegative_forces_ground_nonnegative

end Millennium.RH.SemilocalGroundStateShiftFirewall
