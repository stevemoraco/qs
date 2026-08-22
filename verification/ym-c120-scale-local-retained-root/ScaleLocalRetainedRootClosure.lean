import Mathlib

/-!
# Scale-local retained-root absorption

Finite real-algebra companion to the source/dependency repair of the weak-scale
one/two-root estimate.  A strict nonroot branch factor can be absorbed while a
fixed retained-root cost changes only the prefactor.  The same branch factor
works for one and two retained roots, and a later fixed bounded handoff changes
only that prefactor.

This file does not formalize Kirk's Banach spaces, replica--BKAR, the weak
renormalization group, multiscale forests, Osterwalder--Schrader reconstruction,
Yang--Mills theory, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.ScaleLocalRetainedRootClosure

/-- If a rooted majorant satisfies `total ≤ root + branch * total` with a
strict branch factor, then all nonroot descendants are absorbed into the fixed
root prefactor.  No smallness assumption on `root` is required. -/
theorem rooted_recursion_absorbed
    (root branch total : ℝ)
    (hbranch : branch < 1)
    (hrec : total ≤ root + branch * total) :
    total ≤ root / (1 - branch) := by
  have hden : 0 < 1 - branch := sub_pos.mpr hbranch
  apply (le_div_iff₀ hden).2
  nlinarith

/-- One-root and two-root rows may have different fixed root constants while
sharing exactly the same strict nonroot branch factor. -/
theorem one_two_root_rows_share_branch_factor
    (rootOne rootTwo branch totalOne totalTwo : ℝ)
    (hbranch : branch < 1)
    (hone : totalOne ≤ rootOne + branch * totalOne)
    (htwo : totalTwo ≤ rootTwo + branch * totalTwo) :
    totalOne ≤ rootOne / (1 - branch) ∧
      totalTwo ≤ rootTwo / (1 - branch) := by
  constructor
  · exact rooted_recursion_absorbed rootOne branch totalOne hbranch hone
  · exact rooted_recursion_absorbed rootTwo branch totalTwo hbranch htwo

/-- A fixed bounded map out of the retained-root space preserves the strict
branch denominator and changes only the prefactor. -/
theorem bounded_handoff_preserves_rooted_denominator
    (root branch total output handoff : ℝ)
    (hbranch : branch < 1)
    (hhandoff : 0 ≤ handoff)
    (hrec : total ≤ root + branch * total)
    (hout : output ≤ handoff * total) :
    output ≤ handoff * (root / (1 - branch)) := by
  have htotal := rooted_recursion_absorbed root branch total hbranch hrec
  exact hout.trans (mul_le_mul_of_nonneg_left htotal hhandoff)

#print axioms rooted_recursion_absorbed
#print axioms one_two_root_rows_share_branch_factor
#print axioms bounded_handoff_preserves_rooted_denominator

end Millennium.YangMills.ScaleLocalRetainedRootClosure
