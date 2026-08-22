import Mathlib

/-!
# B218/B218A finite ground-state Haar algebra

Finite algebra only.

This file formalizes the load-bearing scalar identities behind the B218/B218A
human proofs:

* the two branchwise first-order factorizations of the positive tent;
* branchwise nonnegativity;
* the exact tent-mass ledger;
* completion of squares for the ground-state transform;
* the hostile intermediate-exponent ledger;
* the exact zeroth/first Haar-square moments and diagonal constants.

It does **not** formalize derivatives, integrals, prime sums, PNT/Stieltjes
asymptotics, B129/B131/B217, zeta, Xi, Deng--Yang--Lu, B46, RH, or not-RH.
-/

namespace RHB218GroundStateHaarFinite

/-- Algebraic left-branch identity. In the analytic proof `z` is the
appropriate exponential derivative and `2 * (z - 1)` is the left branch of
the compact primitive. -/
theorem left_branch_factor (z : ℝ) :
    z - (2 * (z - 1)) / 2 = 1 := by
  ring

/-- Algebraic right-branch identity. In the analytic proof `-z` is the
exponential derivative and `2 * (c - z)` is the right branch of the compact
primitive. -/
theorem right_branch_factor (c z : ℝ) :
    -z - (2 * (c - z)) / 2 = -c := by
  ring

/-- The left tent branch is nonnegative once its exponential coordinate is at
least one. -/
theorem left_tent_nonnegative (z : ℝ) (hz : 1 ≤ z) :
    0 ≤ 2 * (z - 1) := by
  linarith

/-- The right tent branch is nonnegative once its exponential coordinate is at
most `c`. -/
theorem right_tent_nonnegative (c z : ℝ) (hz : z ≤ c) :
    0 ≤ 2 * (c - z) := by
  linarith

/-- Exact finite ledger behind the total tent mass `2 h (c - 1)`. The two
parenthesized terms are the analytically integrated left and right branches. -/
theorem tent_mass_ledger (h c : ℝ) :
    2 * (c * h - 2 * (c - 1)) +
        2 * (2 * (c - 1) - h) =
      2 * h * (c - 1) := by
  ring

/-- Scalar completion of squares behind
`|F' - F/2|^2 = |F'|^2 + |F|^2/4 - F'F`. -/
theorem ground_state_square_completion (x y : ℝ) :
    (x - y / 2) ^ 2 = x ^ 2 + y ^ 2 / 4 - x * y := by
  ring

/-- Exact exponent ledger for an intermediate mode:
`exp(t) * exp(-2 (1/2-delta) t) = exp(2 delta t)`. -/
theorem hostile_mode_exponent (delta : ℝ) :
    1 - 2 * ((1 : ℝ) / 2 - delta) = 2 * delta := by
  ring

/-- Squaring the exact marked relation `S = w * G'` gives the weighted energy
identity pointwise. -/
theorem marked_square_identity (w g : ℝ) :
    (w * g) ^ 2 = w ^ 2 * g ^ 2 := by
  ring

/-- Zeroth Haar-square moment ledger: one interval has weight one and the
other has weight `c^2`. -/
theorem haar_square_mass (h c : ℝ) :
    h + c ^ 2 * h = h * (1 + c ^ 2) := by
  ring

/-- First signed Haar-square moment ledger. -/
theorem haar_square_first_moment (h c : ℝ) :
    -h ^ 2 / 2 + c ^ 2 * h ^ 2 / 2 = h ^ 2 * (c ^ 2 - 1) / 2 := by
  ring

/-- With `L=4h`, the leading diagonal coefficient simplifies to
`16 h^3 (1+c^2)`. -/
theorem diagonal_leading_constant (h c : ℝ) :
    (4 * h) ^ 2 * h * (1 + c ^ 2) = 16 * h ^ 3 * (1 + c ^ 2) := by
  ring

/-- With `L=4h`, the constant diagonal term simplifies to
`h^3 (10+6c^2)`. -/
theorem diagonal_constant_term (h c : ℝ) :
    ((4 * h) ^ 2 / 2) * h * (1 + c ^ 2) -
        ((4 * h) * h ^ 2 / 2) * (c ^ 2 - 1) =
      h ^ 3 * (10 + 6 * c ^ 2) := by
  ring

#print axioms left_branch_factor
#print axioms right_branch_factor
#print axioms left_tent_nonnegative
#print axioms right_tent_nonnegative
#print axioms tent_mass_ledger
#print axioms ground_state_square_completion
#print axioms hostile_mode_exponent
#print axioms marked_square_identity
#print axioms haar_square_mass
#print axioms haar_square_first_moment
#print axioms diagonal_leading_constant
#print axioms diagonal_constant_term

end RHB218GroundStateHaarFinite
