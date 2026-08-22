import Mathlib

/-!
# RH B212 isolated crossing determinant — finite algebra only

This file formalizes the load-bearing real algebra behind RH #1127 / B212.

For one isolated entering conjugate-pair crossing with normalized coordinate
`a ± i b` and multiplicity `n`, the first three drift-corrected moments are

`j0 = 2n`, `j1 = 2na`, `j2 = 2n(a^2-b^2)`.

Their first Hankel determinant is exactly `-4 n^2 b^2`, and hence the first
three coefficients recover the squared transverse displacement.  A single real
node has zero determinant.

The hostile mixed-event calculation is also formalized: two real nodes `±1`
together with a nonreal pair `a ± i b` on the same normalized unit circle can
have *positive* first Hankel determinant.  Thus event isolation is an independent
load-bearing hypothesis; the 2x2 determinant is not a test for arbitrary
unresolved simultaneous events.

The final algebra lemma records uniqueness of a real collision centre for a
second node with different real coordinate.  It is the finite polynomial step
used by B212's rational-centre isolation argument.

This source does NOT formalize Xi, zeta zeros, contour integrals, Deng--Yang--Lu,
B46, RH, not-RH, discreteness of zero sets, or the global rational-centre
isolation theorem.
-/

namespace RHB212CrossingDeterminantFinite

/-- First jump moment of one isolated conjugate-pair event. -/
def j0 (n : ℝ) : ℝ := 2 * n

/-- Second jump moment of one isolated conjugate-pair event. -/
def j1 (n a : ℝ) : ℝ := 2 * n * a

/-- Third jump moment of one isolated conjugate-pair event. -/
def j2 (n a b : ℝ) : ℝ := 2 * n * (a ^ 2 - b ^ 2)

/-- Exact isolated-pair Hankel determinant. -/
theorem isolated_pair_determinant (n a b : ℝ) :
    j0 n * j2 n a b - (j1 n a) ^ 2 = -4 * n ^ 2 * b ^ 2 := by
  simp only [j0, j1, j2]
  ring

/-- Denominator-cleared exact recovery of the squared transverse displacement. -/
theorem isolated_pair_depth_recovery (n a b : ℝ) :
    (j1 n a) ^ 2 - j0 n * j2 n a b = (j0 n) ^ 2 * b ^ 2 := by
  simp only [j0, j1, j2]
  ring

/-- With positive multiplicity and nonzero transverse displacement, the first
Hankel determinant is strictly negative. -/
theorem isolated_pair_determinant_negative
    {n a b : ℝ} (hn : 0 < n) (hb : b ≠ 0) :
    j0 n * j2 n a b - (j1 n a) ^ 2 < 0 := by
  rw [isolated_pair_determinant]
  have hn2 : 0 < n ^ 2 := sq_pos_of_pos hn
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  positivity

/-- If the multiplicity is nonzero, division by `j0^2` recovers `b^2` exactly. -/
theorem isolated_pair_depth_ratio
    {n a b : ℝ} (hn : n ≠ 0) :
    ((j1 n a) ^ 2 - j0 n * j2 n a b) / (j0 n) ^ 2 = b ^ 2 := by
  rw [isolated_pair_depth_recovery]
  have hj0 : j0 n ≠ 0 := by
    simp [j0, hn]
  field_simp [hj0]

/-- A single real node has zero first Hankel determinant. -/
theorem single_real_node_determinant_zero (n u : ℝ) :
    n * (n * u ^ 2) - (n * u) ^ 2 = 0 := by
  ring

/-- For the hostile mixed event consisting of real nodes `±1` and a conjugate
pair `a ± i b` on the unit circle, the second raw moment simplifies to `4a^2`. -/
theorem mixed_event_second_moment
    {a b : ℝ} (hcircle : a ^ 2 + b ^ 2 = 1) :
    (2 : ℝ) + 2 * (a ^ 2 - b ^ 2) = 4 * a ^ 2 := by
  nlinarith

/-- The hostile mixed event can have a positive first Hankel determinant even
though it contains a nonreal pair. -/
theorem mixed_event_positive_determinant
    {a b : ℝ} (hcircle : a ^ 2 + b ^ 2 = 1) (ha : a ≠ 0) :
    (4 : ℝ) * ((2 : ℝ) + 2 * (a ^ 2 - b ^ 2)) - (2 * a) ^ 2 > 0 := by
  rw [mixed_event_second_moment hcircle]
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  nlinarith

/-- Equal-distance collision with a node having different real coordinate
excludes at most one real centre.  This is the polynomial core of the global
rational-centre isolation argument. -/
theorem equal_distance_collision_center_unique
    {x y gamma delta c₁ c₂ : ℝ}
    (hx : x ≠ gamma)
    (h₁ : x ^ 2 + y ^ 2 - gamma ^ 2 - delta ^ 2
      - 2 * c₁ * (x - gamma) = 0)
    (h₂ : x ^ 2 + y ^ 2 - gamma ^ 2 - delta ^ 2
      - 2 * c₂ * (x - gamma) = 0) :
    c₁ = c₂ := by
  have hprod : (c₁ - c₂) * (x - gamma) = 0 := by
    nlinarith [h₁, h₂]
  rcases mul_eq_zero.mp hprod with hc | hxzero
  · linarith
  · exact False.elim (hx (sub_eq_zero.mp hxzero))

#print axioms isolated_pair_determinant
#print axioms isolated_pair_depth_recovery
#print axioms isolated_pair_determinant_negative
#print axioms isolated_pair_depth_ratio
#print axioms single_real_node_determinant_zero
#print axioms mixed_event_second_moment
#print axioms mixed_event_positive_determinant
#print axioms equal_distance_collision_center_unique

end RHB212CrossingDeterminantFinite
