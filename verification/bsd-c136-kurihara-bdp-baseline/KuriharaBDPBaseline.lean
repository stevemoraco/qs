import Mathlib

namespace Millennium.BSD.KuriharaBDPBaseline

/-- Rewritten without truncated subtraction: `rho ≥ 2*(m-1)` with `m≥1`
    is equivalent to the linear inequality `2*m ≤ rho+2`. -/
theorem augmentationWindowRankCap
    (m rho R : ℕ)
    (hbase : 2 * m ≤ rho + 2)
    (hsmall : rho < 2 * R) :
    m ≤ R := by
  omega

/-- Every nonnegative baseline inequality has an exact additive defect. -/
theorem baselineDefectExists
    (baseline rho : ℕ)
    (hbase : baseline ≤ rho) :
    ∃ delta : ℕ, rho = baseline + delta := by
  omega

/-- Vanishing of the additive defect is exactly baseline equality. -/
theorem zeroDefectIffBaselineEquality
    (baseline rho delta : ℕ)
    (hledger : rho = baseline + delta) :
    delta = 0 ↔ rho = baseline := by
  omega

/-- A width-two window above the baseline leaves at most one unit of defect. -/
theorem oneUnitExcessWindow
    (baseline rho delta : ℕ)
    (hledger : rho = baseline + delta)
    (hwindow : rho < baseline + 2) :
    delta ≤ 1 := by
  omega

/-- If the exact augmentation order equals the baseline, its defect is zero. -/
theorem exactBaselineKillsDefect
    (baseline rho delta : ℕ)
    (hledger : rho = baseline + delta)
    (hexact : rho = baseline) :
    delta = 0 := by
  omega

#print axioms augmentationWindowRankCap
#print axioms baselineDefectExists
#print axioms zeroDefectIffBaselineEquality
#print axioms oneUnitExcessWindow
#print axioms exactBaselineKillsDefect

end Millennium.BSD.KuriharaBDPBaseline
