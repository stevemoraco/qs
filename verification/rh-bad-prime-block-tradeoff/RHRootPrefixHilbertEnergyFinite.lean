import Mathlib

namespace RHRootPrefixHilbertEnergyFinite

/-- Exact weighted square-energy exponent of one unit-length bad-prime block. -/
theorem hilbert_block_exponent_identity
    (delta s epsilon : ℝ) :
    (1 - epsilon) + 2 * (delta - epsilon) - (1 + 2 * s)
      = 2 * (delta - s) - 3 * epsilon := by
  ring

/-- The square-energy block grows whenever the depth gap dominates the three
copies of the clean block loss. -/
theorem hilbert_block_exponent_positive
    {delta s epsilon : ℝ}
    (h : 3 * epsilon < 2 * (delta - s)) :
    0 < 2 * (delta - s) - 3 * epsilon := by
  linarith

/-- A pointwise root bound `|R| <= p^(delta+eta)` leaves a positive quadratic
summability margin whenever `delta+eta<s`. -/
theorem hilbert_upper_margin_positive
    {delta s eta : ℝ}
    (h : delta + eta < s) :
    0 < 2 * (s - delta - eta) := by
  linarith

/-- Multiplying a root response by a factor whose square is bounded below by
`c² p` transfers the corresponding square lower bound. -/
theorem factor_square_lower
    {c2 p factor root defect : ℝ}
    (hscale : c2 * p ≤ factor ^ 2)
    (hdefect : defect = factor * root) :
    c2 * p * root ^ 2 ≤ defect ^ 2 := by
  have hmul := mul_le_mul_of_nonneg_right hscale (sq_nonneg root)
  rw [hdefect]
  nlinarith

/-- The analogous factor-square upper bound. -/
theorem factor_square_upper
    {C2 p factor root defect : ℝ}
    (hscale : factor ^ 2 ≤ C2 * p)
    (hdefect : defect = factor * root) :
    defect ^ 2 ≤ C2 * p * root ^ 2 := by
  have hmul := mul_le_mul_of_nonneg_right hscale (sq_nonneg root)
  rw [hdefect]
  nlinarith

/-- The factorized defect denominator has one additional power of the prime,
matching the square-root-sized factor. -/
theorem factorized_denominator_exponent
    (s : ℝ) :
    2 + 2 * s = 1 + (1 + 2 * s) := by
  ring

/-- The quadratic moment frontier is twice the horizontal zero depth when the
series parameter is written without the conventional factor two. -/
theorem quadratic_frontier_scale
    (delta : ℝ) :
    2 * delta / 2 = delta := by
  ring

/-- A false-RH depth strictly to the right of a Hilbert line leaves a positive
frontier gap. -/
theorem hilbert_line_gap_positive
    {delta s : ℝ}
    (h : s < delta) :
    0 < 2 * (delta - s) := by
  linarith

/-- Every positive Hilbert parameter lies to the right of the zero frontier
when that frontier is zero. -/
theorem rh_all_positive_lines
    {s : ℝ}
    (hs : 0 < s) :
    0 < 2 * (s - 0) := by
  linarith

#print axioms hilbert_block_exponent_identity
#print axioms hilbert_block_exponent_positive
#print axioms hilbert_upper_margin_positive
#print axioms factor_square_lower
#print axioms factor_square_upper
#print axioms factorized_denominator_exponent
#print axioms quadratic_frontier_scale
#print axioms hilbert_line_gap_positive
#print axioms rh_all_positive_lines

end RHRootPrefixHilbertEnergyFinite
