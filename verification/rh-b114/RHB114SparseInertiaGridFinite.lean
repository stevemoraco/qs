import Mathlib

/-!
# RH B114 sparse shifted-inertia grid finite core

This file formalizes only the finite ordered-real algebra behind the B114
logarithmic shift-grid reduction.

It does not formalize primes, zeta, the B109B centered-gap stream, asymptotics,
negative index of matrices, the PNT ceiling, or the Riemann hypothesis.
-/

namespace RHB114SparseInertiaGridFinite

/-- A live threshold bracket transfers a sampled weak-L1 bound with exactly the
multiplicative grid-ratio loss. -/
theorem bracketed_threshold_transfer
    {lam lamLow rho count countLow G : ℝ}
    (hlow0 : 0 ≤ lamLow)
    (hrho0 : 0 ≤ rho)
    (hbracketHigh : lam ≤ rho * lamLow)
    (hcount0 : 0 ≤ count)
    (hcount : count ≤ countLow)
    (hsampled : lamLow * countLow ≤ G) :
    lam * count ≤ rho * G := by
  have h1 : lam * count ≤ (rho * lamLow) * count := by
    exact mul_le_mul_of_nonneg_right hbracketHigh hcount0
  have h2 : (rho * lamLow) * count ≤ (rho * lamLow) * countLow := by
    have hcoef : 0 ≤ rho * lamLow := mul_nonneg hrho0 hlow0
    exact mul_le_mul_of_nonneg_left hcount hcoef
  have h3 : (rho * lamLow) * countLow = rho * (lamLow * countLow) := by
    ring
  have h4 : rho * (lamLow * countLow) ≤ rho * G := by
    exact mul_le_mul_of_nonneg_left hsampled hrho0
  calc
    lam * count ≤ (rho * lamLow) * count := h1
    _ ≤ (rho * lamLow) * countLow := h2
    _ = rho * (lamLow * countLow) := h3
    _ ≤ rho * G := h4

/-- The ultra-small-depth endpoint is paid by dimension alone. -/
theorem tiny_threshold_paid_by_dimension
    {lam count dim : ℝ}
    (hdim0 : 0 < dim)
    (hcount0 : 0 ≤ count)
    (hcount : count ≤ dim)
    (hlam : lam ≤ 1 / dim) :
    lam * count ≤ 1 := by
  have h1 : lam * count ≤ (1 / dim) * dim := by
    exact mul_le_mul hlam hcount hcount0 (by positivity)
  have hdimne : dim ≠ 0 := ne_of_gt hdim0
  calc
    lam * count ≤ (1 / dim) * dim := h1
    _ = 1 := by field_simp [hdimne]

/-- If a threshold already exceeds every possible positive depth, its count is
zero and hence its weak product vanishes. -/
theorem above_ceiling_has_zero_product
    {lam count : ℝ} (hcount : count = 0) :
    lam * count = 0 := by
  rw [hcount, mul_zero]

/-- Exact multiplicative interpolation step used by the geometric grid. -/
theorem geometric_grid_step
    {lamPrev lam rho : ℝ}
    (hstep : lamPrev = rho * lam) :
    lamPrev = rho * lam := hstep

/-- Hostile one-gap witness. If the lower sampled threshold has dimension
product one and the next sampled threshold is `rho` times larger, then a depth
placed inside the multiplicative gap can have true weak product `rho/2` while
the lower sampled product remains one. -/
theorem fixed_gap_can_hide_depth
    {dim lamLow rho : ℝ}
    (hlow0 : 0 < lamLow)
    (hrho : 2 < rho)
    (hnorm : dim * lamLow = 1) :
    let x := lamLow * rho / 2
    lamLow < x ∧ x < rho * lamLow ∧ dim * x = rho / 2 := by
  dsimp
  constructor
  · have hscaled : 2 * lamLow < rho * lamLow := by
      exact mul_lt_mul_of_pos_right hrho hlow0
    nlinarith
  constructor
  · have hpos : 0 < rho * lamLow := mul_pos (by linarith) hlow0
    nlinarith
  · calc
      dim * (lamLow * rho / 2) = (dim * lamLow) * rho / 2 := by ring
      _ = rho / 2 := by rw [hnorm]

/-- The hostile witness's sampled lower-threshold product is exactly one. -/
theorem fixed_gap_lower_sample_is_one
    {dim lamLow : ℝ}
    (hnorm : dim * lamLow = 1) :
    lamLow * dim = 1 := by
  calc
    lamLow * dim = dim * lamLow := by ring
    _ = 1 := hnorm

/-- A finite multiplicative comparison closes by transitivity. -/
theorem sampled_bound_closes_true_bound
    {true sampled rho target : ℝ}
    (htrue : true ≤ rho * sampled)
    (hbudget : rho * sampled ≤ target) :
    true ≤ target := htrue.trans hbudget

#print axioms bracketed_threshold_transfer
#print axioms tiny_threshold_paid_by_dimension
#print axioms above_ceiling_has_zero_product
#print axioms geometric_grid_step
#print axioms fixed_gap_can_hide_depth
#print axioms fixed_gap_lower_sample_is_one
#print axioms sampled_bound_closes_true_bound

end RHB114SparseInertiaGridFinite
