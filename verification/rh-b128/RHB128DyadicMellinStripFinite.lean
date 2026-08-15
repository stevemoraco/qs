import Mathlib

/-!
# RH B128 dyadic Mellin / Hermite finite core

Finite real algebra only.

This file formalizes the exponent bookkeeping behind the B128 dyadic Mellin
criterion and the exact two-dimensional Hermite-Sylvester obstruction for one
nonreal conjugate root pair.

It does **not** formalize the von Mangoldt function, Mellin transforms, zeta,
analytic continuation, Newton identities, the global Hermite-Sylvester theorem,
BGST/Hankel pencils, or the Riemann hypothesis.
-/

namespace RHB128DyadicMellinStripFinite

/-- Fixed-q strip boundary used in the preceding B118/B127 ladder. -/
def sigmaQ (q : ℝ) : ℝ := (1 : ℝ) / 2 + 1 / (2 * q)

/-- Hölder-conjugate moment exponent. -/
def pQ (q : ℝ) : ℝ := q / (q - 1)

/-- Exact exponent identity: the B127 moment exponent is `p + 1/2`. -/
theorem fixed_q_critical_exponent
    (q : ℝ) (hq1 : q ≠ 1) (hq0 : q ≠ 0) :
    pQ q * sigmaQ q + 1 = pQ q + (1 : ℝ) / 2 := by
  dsimp [pQ, sigmaQ]
  field_simp [hq1, hq0]
  ring

/-- Layer-cake exponent cancellation used when weak-Lp depth is integrated. -/
theorem weak_tail_l1_exponent (p sigma : ℝ) :
    p * sigma + 1 + sigma * (1 - p) = sigma + 1 := by
  ring

/-- The RH endpoint dyadic L1 exponent is exactly `3/2`. -/
theorem rh_endpoint_l1_exponent :
    (1 : ℝ) + 1 / 2 = 3 / 2 := by
  norm_num

/-- The q-strip boundary is the symmetric half plus `1/(2q)`. -/
theorem sigmaQ_eq (q : ℝ) :
    sigmaQ q = (1 : ℝ) / 2 + 1 / (2 * q) := by
  rfl

/-! ## One conjugate-pair Hermite matrix shadow -/

For roots `a+ib` and `a-ib`, the first three power sums are
`2`, `2a`, and `2(a^2-b^2)`.  The corresponding 2x2 Hermite matrix has quadratic
form below.
-/

/-- Quadratic form of the two-root Hermite matrix. -/
def hermitePairQ (a b x y : ℝ) : ℝ :=
  2 * x ^ 2 + 4 * a * x * y + 2 * (a ^ 2 - b ^ 2) * y ^ 2

/-- Exact completion of squares: nonreal displacement is the only negative term. -/
theorem hermite_pair_completion (a b x y : ℝ) :
    hermitePairQ a b x y = 2 * (x + a * y) ^ 2 - 2 * b ^ 2 * y ^ 2 := by
  dsimp [hermitePairQ]
  ring

/-- The determinant of the conjugate-pair Hermite matrix is `-4 b^2`. -/
theorem hermite_pair_determinant (a b : ℝ) :
    2 * (2 * (a ^ 2 - b ^ 2)) - (2 * a) ^ 2 = -4 * b ^ 2 := by
  ring

/-- Any genuinely nonreal pair supplies an explicit negative Hermite direction. -/
theorem nonreal_pair_has_negative_witness
    (a b : ℝ) (hb : b ≠ 0) :
    hermitePairQ a b (-a) 1 < 0 := by
  rw [hermite_pair_completion]
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  nlinarith

/-- A collapsed pair (`b=0`) gives a positive-semidefinite rank-one shadow. -/
theorem real_pair_shadow_nonnegative
    (a x y : ℝ) :
    0 ≤ hermitePairQ a 0 x y := by
  rw [hermite_pair_completion]
  norm_num
  positivity

#print axioms fixed_q_critical_exponent
#print axioms weak_tail_l1_exponent
#print axioms rh_endpoint_l1_exponent
#print axioms hermite_pair_completion
#print axioms hermite_pair_determinant
#print axioms nonreal_pair_has_negative_witness
#print axioms real_pair_shadow_nonnegative

end RHB128DyadicMellinStripFinite
