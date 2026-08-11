import Mathlib

/-!
# P versus NP audit: the source critical-path count is exactly tight

Honesty status: integer bookkeeping for an explicit circuit topology only. This
file does not formalize Boolean circuit semantics, probabilistic circuits,
hardness magnification, NP, `P != NP`, or any official Millennium statement.

The companion theorem note gives an explicit normalized single-output binary
circuit with `n` inputs and `2*n-2` gates whose input critical paths are pairwise
disjoint and whose variables are all nonisolated. This file protects the exact
node and wire equalities attained by that topology. Consequently no positive
additive surplus can follow from the original counting inequalities alone.
-/

namespace MillenniumBraid
namespace PNPCriticalPathTight

/-- Number of nodes lying on the input critical paths in the equality model. -/
def criticalNodes (n : ℤ) : ℤ := n + 1

/-- Number of nodes outside the input critical paths in the equality model. -/
def outsideNodes (n : ℤ) : ℤ := 2 * n - 3

/-- The total number of gates is total nodes minus the `n` input nodes. -/
def gateCount (n : ℤ) : ℤ :=
  criticalNodes n + outsideNodes n - n

/-- Wires from critical-path nodes to outside nodes. -/
def criticalToOutside (n : ℤ) : ℤ := 2 * n - 2

/-- Wires between outside nodes. -/
def outsideToOutside (n : ℤ) : ℤ := 2 * n - 4

/-- The root of the outside binary tree feeds the output critical-path gate. -/
def outsideToCritical (_n : ℤ) : ℤ := 1

/-- The distinguished input feeds the output gate directly. -/
def criticalToCritical (_n : ℤ) : ℤ := 1

/--
All source bookkeeping inequalities are saturated by the explicit topology.
In particular, total nodes are `3*n-2` and total gates are exactly `2*n-2`.
-/
theorem source_counting_equalities (n : ℤ) :
    criticalNodes n + outsideNodes n = 3 * n - 2 ∧
    gateCount n = 2 * n - 2 ∧
    criticalToOutside n + outsideToOutside n = 2 * outsideNodes n ∧
    outsideToOutside n + outsideToCritical n = outsideNodes n ∧
    criticalToOutside n + outsideToOutside n +
        outsideToCritical n + criticalToCritical n = 2 * gateCount n := by
  constructor
  · simp [criticalNodes, outsideNodes]
    ring
  constructor
  · simp [gateCount, criticalNodes, outsideNodes]
    ring
  constructor
  · simp [criticalToOutside, outsideToOutside, outsideNodes]
    ring
  constructor
  · simp [outsideToOutside, outsideToCritical, outsideNodes]
    ring
  · simp [criticalToOutside, outsideToOutside, outsideToCritical,
      criticalToCritical, gateCount, criticalNodes, outsideNodes]
    ring

/-- For the genuine topology range `n >= 3`, every displayed count is nonnegative. -/
theorem equality_model_counts_nonnegative
    (n : ℤ) (hn : 3 ≤ n) :
    0 ≤ criticalNodes n ∧
    0 ≤ outsideNodes n ∧
    0 ≤ gateCount n ∧
    0 ≤ criticalToOutside n ∧
    0 ≤ outsideToOutside n ∧
    0 ≤ outsideToCritical n ∧
    0 ≤ criticalToCritical n := by
  simp [criticalNodes, outsideNodes, gateCount, criticalToOutside,
    outsideToOutside, outsideToCritical, criticalToCritical]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> norm_num

/--
The equality model falsifies every positive additive strengthening of the
conclusion if no additional structural premise is introduced.
-/
theorem positive_surplus_not_forced_by_source_count
    (n delta : ℤ) (hdelta : 0 < delta) :
    ¬ (2 * n - 2 + delta ≤ gateCount n) := by
  simp [gateCount, criticalNodes, outsideNodes]
  linarith

/-- The equality topology has exactly one outside outgoing wire per outside node. -/
theorem outside_outdegree_budget_saturated (n : ℤ) :
    outsideToOutside n + outsideToCritical n = outsideNodes n := by
  simp [outsideToOutside, outsideToCritical, outsideNodes]
  ring

#print axioms source_counting_equalities
#print axioms equality_model_counts_nonnegative
#print axioms positive_surplus_not_forced_by_source_count
#print axioms outside_outdegree_budget_saturated

end PNPCriticalPathTight
end MillenniumBraid
