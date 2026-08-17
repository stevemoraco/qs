import Mathlib

namespace Millennium.BSD.KuriharaBDPBaseline

theorem baselineWindowBoundsMax
    (m rho R : ℕ)
    (hm : 1 ≤ m)
    (hbase : 2 * (m - 1) ≤ rho)
    (hwindow : rho < 2 * R) :
    m ≤ R := by
  omega

theorem baselineDefectExists
    (m rho : ℕ)
    (hm : 1 ≤ m)
    (hbase : 2 * (m - 1) ≤ rho) :
    ∃ delta : ℕ, rho = 2 * (m - 1) + delta := by
  refine ⟨rho - 2 * (m - 1), ?_⟩
  omega

theorem zeroDefectIffBaselineEquality
    (baseline rho delta : ℕ)
    (hledger : rho = baseline + delta) :
    delta = 0 ↔ rho = baseline := by
  omega

theorem oneUnitExcessWindow
    (baseline rho delta : ℕ)
    (hledger : rho = baseline + delta)
    (hwindow : rho < baseline + 2) :
    delta ≤ 1 := by
  omega

theorem augmentationWindowRankCap
    (m rho R : ℕ)
    (hm : 1 ≤ m)
    (hbase : 2 * (m - 1) ≤ rho)
    (hsmall : rho < 2 * R) :
    m ≤ R := by
  exact baselineWindowBoundsMax m rho R hm hbase hsmall

#print axioms baselineWindowBoundsMax
#print axioms baselineDefectExists
#print axioms zeroDefectIffBaselineEquality
#print axioms oneUnitExcessWindow
#print axioms augmentationWindowRankCap

end Millennium.BSD.KuriharaBDPBaseline
