import Mathlib

/-!
# BSD discrete-order two-defect algebra

Finite integer bookkeeping only. Deep arithmetic inputs such as an equality
between a discrete Kurihara order and Selmer corank are hypotheses here.

This file proves no case of the Birch--Swinnerton--Dyer conjecture by itself.
-/

namespace Millennium.BSD.DiscreteOrderDefect

/-- If the supplied discrete order equals Selmer corank and Selmer corank splits
as Mordell--Weil rank plus the `p`-primary Sha corank, then the BSD rank defect
splits exactly into a complex/discrete defect plus the Sha-corank defect. -/
theorem twoDefect_identity
    (rAn rMW rSel rDelta rSha : ℤ)
    (hDiscrete : rSel = rDelta)
    (hSelmer : rSel = rMW + rSha) :
    rAn - rMW = (rAn - rDelta) + rSha := by
  omega

/-- Vanishing of both remaining defects closes rank equality at the finite
bookkeeping level. -/
theorem zeroDefects_imply_rankEquality
    (rAn rMW rSel rDelta rSha : ℤ)
    (hDiscrete : rSel = rDelta)
    (hSelmer : rSel = rMW + rSha)
    (hAnalytic : rAn = rDelta)
    (hSha : rSha = 0) :
    rAn = rMW := by
  omega

/-- Under the two structural equalities, official rank equality is equivalent
to the two residual defects summing to zero. -/
theorem rankEquality_iff_twoDefectSum_zero
    (rAn rMW rSel rDelta rSha : ℤ)
    (hDiscrete : rSel = rDelta)
    (hSelmer : rSel = rMW + rSha) :
    rAn = rMW ↔ (rAn - rDelta) + rSha = 0 := by
  constructor <;> intro h <;> omega

#print axioms twoDefect_identity
#print axioms zeroDefects_imply_rankEquality
#print axioms rankEquality_iff_twoDefectSum_zero

end Millennium.BSD.DiscreteOrderDefect
