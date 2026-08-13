import Mathlib

namespace NSSparseTriadCapacity

/-- Throughout the physical viscous window, Palasek's adjacent-scale restriction
    `b < alpha/2` forces the three-dimensional sparse packing exponent to stay
    strictly below the low-output population exponent required for an
    `N^alpha` coefficient. -/
theorem sparse_exponent_strictly_too_small
    {alpha b : ℝ}
    (halpha : 2 < alpha)
    (hb : b < alpha / 2) :
    3 * (b - 1) < 2 * alpha - 2 := by
  linarith

/-- At the test exponent alpha=9/4 and the maximal Palasek endpoint b<5/4,
    sparse packing grows with exponent below 3/4 while the required low-output
    population has exponent exactly 5/2. -/
theorem nine_fourths_sparse_firewall
    {b : ℝ} (hb : b < (5 : ℝ) / 4) :
    3 * (b - 1) < (5 : ℝ) / 2 := by
  linarith

/-- The required Fourier-output population exponent at alpha=9/4. -/
theorem nine_fourths_required_population :
    2 * ((9 : ℝ) / 4) - 2 = (5 : ℝ) / 2 := by
  norm_num

/-- Even the generous endpoint sparse exponent 3/4 is far below 5/2. -/
theorem endpoint_gap :
    (3 : ℝ) / 4 < (5 : ℝ) / 2 := by
  norm_num

#print axioms sparse_exponent_strictly_too_small
#print axioms nine_fourths_sparse_firewall
#print axioms nine_fourths_required_population
#print axioms endpoint_gap

end NSSparseTriadCapacity
