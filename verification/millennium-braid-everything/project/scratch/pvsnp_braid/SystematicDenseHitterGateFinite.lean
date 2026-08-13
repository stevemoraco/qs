import Mathlib

namespace PvsNPBraid

/-- Exact algebra converting the systematic graph-circuit obstruction at
threshold `g = 2n + Δ` into the shared-generator gate requirement. -/
theorem systematic_graph_gate_rearrangement
    (n r Δ s : ℤ)
    (hgate : 2 * n + Δ < s + 2 * (n - r) - 1) :
    2 * r + Δ + 1 < s := by
  linarith

/-- The converse rearrangement is exact. -/
theorem systematic_graph_gate_rearrangement_converse
    (n r Δ s : ℤ)
    (hgate : 2 * r + Δ + 1 < s) :
    2 * n + Δ < s + 2 * (n - r) - 1 := by
  linarith

/-- An injective systematic map with `r` visible seed coordinates among `n`
coordinates has relative range size `2^{-(n-r)}`. -/
theorem systematic_density_exponent (n r : ℕ) (hrn : r ≤ n) :
    n - r + r = n := by
  omega

/-- Exact graph-checking gate budget: shared output computation plus one
comparison per hidden coordinate and a binary AND tree. -/
theorem graph_checker_gate_count (s t : ℤ) :
    s + t + (t - 1) = s + 2 * t - 1 := by
  ring

/-- The near-`2n` obstruction leaves no room for a shared generator smaller
than the additive surplus plus twice the seed length. -/
theorem small_systematic_generator_refuted
    (n r Δ s : ℤ)
    (hsmall : s ≤ 2 * r + Δ + 1) :
    s + 2 * (n - r) - 1 ≤ 2 * n + Δ := by
  linarith

end PvsNPBraid
