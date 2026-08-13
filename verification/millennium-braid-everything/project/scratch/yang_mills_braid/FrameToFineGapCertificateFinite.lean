import Mathlib

namespace YangMillsBraid

/-- Combining a coarse spectral-radius bound with the lower reverse-RG
comparison yields the exact fine eigenvalue-power bound. -/
theorem frame_to_fine_spectral_bound
    (lambdaFine lambdaCoarse q etaFactor leakageKeep : ℝ)
    (hleak : 0 < leakageKeep)
    (hcoarse : lambdaCoarse ≤ q)
    (hreverse : leakageKeep * lambdaFine ≤ etaFactor * lambdaCoarse) :
    lambdaFine ≤ etaFactor * q / leakageKeep := by
  have h1 : leakageKeep * lambdaFine ≤ etaFactor * q := by
    calc
      leakageKeep * lambdaFine ≤ etaFactor * lambdaCoarse := hreverse
      _ ≤ etaFactor * q := by
        by_cases heta : 0 ≤ etaFactor
        · exact mul_le_mul_of_nonneg_left hcoarse heta
        · have : etaFactor * q ≤ etaFactor * lambdaCoarse :=
            mul_le_mul_of_nonpos_left hcoarse heta
          linarith
  exact (le_div_iff₀ hleak).2 h1

/-- The scalar strict-gap condition is exactly that the defect-inflated coarse
base remain below the surviving excited fraction. -/
theorem positive_gap_budget
    (etaFactor q leakageKeep : ℝ)
    (h : etaFactor * q < leakageKeep) :
    etaFactor * q / leakageKeep < 1 := by
  have hkeep : 0 < leakageKeep := by
    by_contra hnot
    have : leakageKeep ≤ 0 := le_of_not_gt hnot
    nlinarith
  exact (div_lt_one hkeep).2 h

/-- Losses add after logarithmic conversion; this is the finite algebra behind
the multiscale physical-gap ledger. -/
theorem additive_gap_budget
    (anchor formLoss leakageLoss : ℝ) :
    anchor - (formLoss + leakageLoss) =
      anchor - formLoss - leakageLoss := by
  ring

end YangMillsBraid
