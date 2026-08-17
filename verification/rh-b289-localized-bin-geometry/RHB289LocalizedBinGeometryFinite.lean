import Mathlib

/-!
# RH B289 finite localized-bin geometry

This file formalizes only the new load-bearing finite geometric fact used by
RH #1559 / B289. It does not formalize primes, asymptotics, Suzuki, Mellin or
Landau arguments, zeta, BGST, B46, RH, or not-RH.
-/

namespace RHB289LocalizedBinGeometry

/-- On a factor-3/2 positive bin, the midpoint `5a/4` is within one quarter
of every point, relative to that point. This is the finite geometric input
behind B289's `16^{-m}` even-power slack. -/
theorem geometric_bin_ratio
    (a u : ℝ)
    (ha : 0 ≤ a)
    (hlo : a ≤ u)
    (hhi : u ≤ 3 * a / 2) :
    |u - 5 * a / 4| ≤ u / 4 := by
  rw [abs_le]
  constructor <;> nlinarith

#print axioms geometric_bin_ratio

end RHB289LocalizedBinGeometry
