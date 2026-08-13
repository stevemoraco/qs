import Mathlib

namespace RHBadPrimeMomentTradeoff

/-- Exact power of one two-loss bad-prime block in the order-`r` positive
moment Dirichlet series. -/
theorem moment_block_exponent_identity
    (r delta sigma a b : ℝ) :
    (1 - a - b) + r * (delta - a) - (1 + sigma)
      = r * delta - sigma - (r + 1) * a - b := by
  ring

/-- The block moment grows polynomially whenever the total weighted loss
`(r+1)a+b` is smaller than the frontier gap `r*delta-sigma`. -/
theorem moment_block_exponent_positive
    {r delta sigma a b : ℝ}
    (h : (r + 1) * a + b < r * delta - sigma) :
    0 < r * delta - sigma - (r + 1) * a - b := by
  linarith

/-- A pointwise depth upper bound `delta+eta` leaves a summable exponent margin
whenever `r(delta+eta)<sigma`. -/
theorem moment_upper_margin_positive
    {r delta sigma eta : ℝ}
    (h : r * (delta + eta) < sigma) :
    0 < sigma - r * delta - r * eta := by
  linarith

/-- The exact unit-coefficient block exponent after using the clean depth
`delta-epsilon` and length exponent `1-epsilon`. -/
theorem unit_block_moment_exponent_identity
    (r delta sigma epsilon : ℝ) :
    (1 - epsilon) + r * (delta - epsilon) - (1 + sigma)
      = r * delta - sigma - (r + 1) * epsilon := by
  ring

/-- The unit-block moment grows whenever `(r+1)epsilon` is below the moment
frontier gap. -/
theorem unit_block_moment_positive
    {r delta sigma epsilon : ℝ}
    (h : (r + 1) * epsilon < r * delta - sigma) :
    0 < r * delta - sigma - (r + 1) * epsilon := by
  linarith

/-- The unweighted local moment carried by a clean bad block has exponent
`1-epsilon+r(delta-epsilon)`. -/
theorem local_moment_exponent_identity
    (r delta epsilon : ℝ) :
    (1 - epsilon) + r * (delta - epsilon)
      = 1 + r * delta - (r + 1) * epsilon := by
  ring

/-- For the quadratic detector, the exact two-loss weighted block exponent is
`2delta-sigma-3a-b`. -/
theorem quadratic_block_exponent_identity
    (delta sigma a b : ℝ) :
    (1 - a - b) + 2 * (delta - a) - (1 + sigma)
      = 2 * delta - sigma - 3 * a - b := by
  ring

/-- For the quadratic detector, the exact unit-block exponent is
`2delta-sigma-3epsilon`. -/
theorem quadratic_unit_block_exponent_identity
    (delta sigma epsilon : ℝ) :
    (1 - epsilon) + 2 * (delta - epsilon) - (1 + sigma)
      = 2 * delta - sigma - 3 * epsilon := by
  ring

/-- Scaling the horizontal depth by a positive moment order preserves strict
ordering of convergence-frontier parameters. -/
theorem moment_frontier_strict
    {r delta sigma : ℝ}
    (hr : 0 < r)
    (h : sigma < delta) :
    r * sigma < r * delta := by
  exact mul_lt_mul_of_pos_left h hr

/-- A positive false-RH depth remains positive after multiplication by every
positive moment order. -/
theorem moment_depth_positive
    {r delta : ℝ}
    (hr : 0 < r)
    (hdelta : 0 < delta) :
    0 < r * delta := by
  exact mul_pos hr hdelta

#print axioms moment_block_exponent_identity
#print axioms moment_block_exponent_positive
#print axioms moment_upper_margin_positive
#print axioms unit_block_moment_exponent_identity
#print axioms unit_block_moment_positive
#print axioms local_moment_exponent_identity
#print axioms quadratic_block_exponent_identity
#print axioms quadratic_unit_block_exponent_identity
#print axioms moment_frontier_strict
#print axioms moment_depth_positive

end RHBadPrimeMomentTradeoff
