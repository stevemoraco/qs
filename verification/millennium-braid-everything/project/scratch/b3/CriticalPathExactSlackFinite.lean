import Mathlib

/-!
# Exact scalar slack behind the critical-path wire count

Finite arithmetic core of the refinement of Fan–Li–Yang Lemma 6.4.
This does not formalize circuit semantics and does not prove P != NP.
-/

namespace Millennium
namespace PvNP

/--
If the exact Type-1→Type-2 and Type-2→Type-2 wire counts sum to the
`2*c2` input wires of the binary-fanin Type-2 gates, then the total gate
count has the exact corrected `2n-2m` form.
-/
theorem criticalPath_exact_slack
    (c1 c2 n m o e1 e2 l : ℤ)
    (h :
      (c1 + n - 2 * o + e1 - l) +
      (c2 - (m - o) + e2 - 2 * (c1 - n) + l) = 2 * c2) :
    c1 + c2 - n = 2 * n - 2 * m + (m - o) + e1 + e2 := by
  omega

/-- Single-output specialization of the exact slack identity. -/
theorem criticalPath_singleOutput_slack
    (g n o e1 e2 : ℤ)
    (h : g = 2 * n - 2 + (1 - o) + e1 + e2) :
    g - (2 * n - 2) = (1 - o) + e1 + e2 := by
  omega

/-- Near-threshold gate count bounds the total nonnegative structural slack. -/
theorem criticalPath_nearThreshold_budget
    (g n s o e1 e2 : ℤ)
    (hident : g = 2 * n - 2 + (1 - o) + e1 + e2)
    (hsmall : g ≤ 2 * n - 2 + s) :
    (1 - o) + e1 + e2 ≤ s := by
  omega

end PvNP
end Millennium
