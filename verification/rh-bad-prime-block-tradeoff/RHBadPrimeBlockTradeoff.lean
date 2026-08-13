import Mathlib

namespace RHBadPrimeBlockTradeoff

/-- The derivative-frontier exponent and the persistence-window exponent add
exactly to the Johnston spike exponent. This is the arithmetic core of the
constant-sized persistence window; no extra exponent loss is necessary. -/
theorem persistence_exponent_identity
    (delta a b : ℝ) :
    (delta - 1 + b) + (1 - a - b) = delta - a := by
  ring

/-- Guth--Maynard's pointwise short-interval exponent `17/30` is strictly
smaller than Huxley's historical exponent `7/12`. -/
theorem guth_maynard_improves_huxley :
    (17 : ℝ) / 30 < (7 : ℝ) / 12 := by
  norm_num

/-- If the two persistence losses sum to less than `13/30`, then the resulting
window exponent lies strictly above the Guth--Maynard `17/30` threshold. -/
theorem guth_maynard_window_admissible
    {a b : ℝ}
    (hab : a + b < (13 : ℝ) / 30) :
    (17 : ℝ) / 30 < 1 - a - b := by
  linarith

/-- The power contributed by one prime-rich bad block to the weighted
Dirichlet series is exactly `delta - sigma - 2a - b`. -/
theorem dirichlet_block_exponent_identity
    (delta sigma a b : ℝ) :
    (1 - a - b) + (delta - a) - (1 + sigma)
      = delta - sigma - 2 * a - b := by
  ring

/-- The block contribution has positive polynomial growth whenever the total
loss `2a+b` is strictly smaller than the gap `delta-sigma`. -/
theorem dirichlet_block_exponent_positive
    {delta sigma a b : ℝ}
    (h : 2 * a + b < delta - sigma) :
    0 < delta - sigma - 2 * a - b := by
  linarith

/-- Symmetric losses `a=b=epsilon/2` produce a near-linear window of exponent
exactly `1-epsilon`. -/
theorem symmetric_window_identity
    (epsilon : ℝ) :
    1 - epsilon / 2 - epsilon / 2 = 1 - epsilon := by
  ring

/-- The symmetric window remains above the current Guth--Maynard threshold
whenever `epsilon<13/30`. -/
theorem symmetric_window_guth_maynard
    {epsilon : ℝ}
    (hepsilon : epsilon < (13 : ℝ) / 30) :
    (17 : ℝ) / 30 < 1 - epsilon / 2 - epsilon / 2 := by
  linarith

/-- The Johnston depth retained by the symmetric choice is stronger than the
clean published threshold `delta-epsilon` whenever `epsilon>0`. -/
theorem symmetric_depth_stronger
    {delta epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    delta - epsilon < delta - epsilon / 2 := by
  linarith

/-- Under symmetric losses, the weighted bad-block exponent is
`delta-sigma-3epsilon/2`. -/
theorem symmetric_dirichlet_exponent_identity
    (delta sigma epsilon : ℝ) :
    delta - sigma - 2 * (epsilon / 2) - epsilon / 2
      = delta - sigma - 3 * epsilon / 2 := by
  ring

/-- Any positive frontier gap `delta-sigma` admits positive symmetric losses
small enough to leave a positive block exponent. -/
theorem symmetric_positive_choice
    {delta sigma epsilon : ℝ}
    (hgap : 0 < delta - sigma)
    (hepsilon : epsilon < 2 * (delta - sigma) / 3) :
    0 < delta - sigma - 3 * epsilon / 2 := by
  linarith

/-- The logarithmic counting-dimension lower exponent `1-epsilon` is positive
for every subunit loss. -/
theorem counting_dimension_positive
    {epsilon : ℝ}
    (hepsilon : epsilon < 1) :
    0 < 1 - epsilon := by
  linarith

#print axioms persistence_exponent_identity
#print axioms guth_maynard_improves_huxley
#print axioms guth_maynard_window_admissible
#print axioms dirichlet_block_exponent_identity
#print axioms dirichlet_block_exponent_positive
#print axioms symmetric_window_identity
#print axioms symmetric_window_guth_maynard
#print axioms symmetric_depth_stronger
#print axioms symmetric_dirichlet_exponent_identity
#print axioms symmetric_positive_choice
#print axioms counting_dimension_positive

end RHBadPrimeBlockTradeoff
