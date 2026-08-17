import Mathlib

namespace Millennium.BSD.HeightOneFittingMidpoint

theorem odd_midpoint
    (c0 c1 f0 f1 f2 : ℕ)
    (h0 : f0 = 2 * c0)
    (h1 : f1 = c0 + c1)
    (h2 : f2 = 2 * c1) :
    2 * f1 = f0 + f2 := by
  omega

theorem paired_drop
    (c0 c1 f0 f1 f2 : ℕ)
    (hc : c1 ≤ c0)
    (h0 : f0 = 2 * c0)
    (h1 : f1 = c0 + c1)
    (h2 : f2 = 2 * c1) :
    f0 - f1 = c0 - c1 ∧ f1 - f2 = c0 - c1 := by
  omega

theorem square_valuation_cancel
    (c d f : ℕ)
    (hc : f = 2 * c)
    (hd : f = 2 * d) :
    c = d := by
  omega

theorem analytic_geometric_gap_agreement
    (c0 c1 d0 d1 f0 f2 : ℕ)
    (hc0 : f0 = 2 * c0)
    (hd0 : f0 = 2 * d0)
    (hc1 : f2 = 2 * c1)
    (hd1 : f2 = 2 * d1) :
    c0 - c1 = d0 - d1 := by
  omega

theorem plateau_collapses_window
    (c0 c1 f0 f1 f2 : ℕ)
    (hc : c0 = c1)
    (h0 : f0 = 2 * c0)
    (h1 : f1 = c0 + c1)
    (h2 : f2 = 2 * c1) :
    f0 = f1 ∧ f1 = f2 := by
  omega

#print axioms odd_midpoint
#print axioms paired_drop
#print axioms square_valuation_cancel
#print axioms analytic_geometric_gap_agreement
#print axioms plateau_collapses_window

end Millennium.BSD.HeightOneFittingMidpoint
