import Mathlib

namespace PNPCriticalPathSlackFinite

/-- Scalar shadow of the exact Type-1/Type-2 wire conservation identity.
The graph-theoretic derivation of the hypothesis is external to this file. -/
theorem exact_slack_identity
    (n c1 c2 o d1 d2 : ℤ)
    (hwire :
      2 * c2 = -c1 + c2 + 3 * n - 1 - o + d1 + d2) :
    (c1 + c2 - n) - (2 * n - 2) = (1 - o) + d1 + d2 := by
  linarith

/-- If the gate count is at most `2n+S`, the exact nonnegative defect mass
is at most `S+2`. -/
theorem frontier_defect_budget
    (n c1 c2 o d1 d2 S : ℤ)
    (hwire :
      2 * c2 = -c1 + c2 + 3 * n - 1 - o + d1 + d2)
    (hsize : c1 + c2 - n ≤ 2 * n + S) :
    (1 - o) + d1 + d2 ≤ S + 2 := by
  have hid := exact_slack_identity n c1 c2 o d1 d2 hwire
  linarith

/-- At the exact `2n-2` baseline, nonnegative defect terms and a Boolean
output-location indicator must all be tight. -/
theorem tight_baseline_forces_zero_defects
    (o d1 d2 : ℤ)
    (ho0 : 0 ≤ o)
    (ho1 : o ≤ 1)
    (hd1 : 0 ≤ d1)
    (hd2 : 0 ≤ d2)
    (htight : (1 - o) + d1 + d2 = 0) :
    o = 1 ∧ d1 = 0 ∧ d2 = 0 := by
  have ho : o = 1 := by linarith
  subst o
  constructor
  · rfl
  constructor <;> linarith

/-- Integer form of the useful frontier substitution: a circuit of size
`2n+S` has at most `S+2` defect units above the `2n-2` skeleton. -/
theorem baseline_to_frontier
    (n S q g : ℤ)
    (hbase : g = 2 * n - 2 + q)
    (hfrontier : g ≤ 2 * n + S) :
    q ≤ S + 2 := by
  linarith

#print axioms exact_slack_identity
#print axioms frontier_defect_budget
#print axioms tight_baseline_forces_zero_defects
#print axioms baseline_to_frontier

end PNPCriticalPathSlackFinite
