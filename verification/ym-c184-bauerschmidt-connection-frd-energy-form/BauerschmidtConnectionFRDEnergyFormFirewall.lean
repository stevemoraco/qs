import Mathlib

/-!
# Bauerschmidt connection-FRD energy-form firewall

Finite scalar consumers for the source-level application of Bauerschmidt's
spectral finite-range decomposition to the dimensionless lattice connection
Laplacian.

The external analytic input has the spectral-multiplier shape

  (1 + t^2 * lambda) * W_t(lambda) <= C

with nonnegative multiplier. The first theorem records that the
energy-normalized multiplier `t^2 * lambda * W_t(lambda)` is then bounded by the
same constant. The second theorem records the exact cancellation of
lattice-spacing powers when a dimensionless covariance piece is rescaled to
physical units.

This file does not formalize Bauerschmidt's theorem, connection Laplacians,
functional calculus, finite propagation, gauge covariance, the interacting
Faizal--Shabir transfer operator, Osterwalder--Schrader reconstruction,
Yang--Mills theory, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.BauerschmidtConnectionFRDEnergyFormFirewall

/-- A Bauerschmidt-type spectral multiplier bound controls the corresponding
energy-normalized multiplier with no heat-kernel hypothesis. -/
theorem energy_multiplier_le_of_resolvent_multiplier_le
    (t lam W C : ℝ)
    (hW : 0 ≤ W)
    (hbound : (1 + t ^ 2 * lam) * W ≤ C) :
    t ^ 2 * lam * W ≤ C := by
  have hfactor : t ^ 2 * lam ≤ 1 + t ^ 2 * lam := by
    linarith
  have hmul : t ^ 2 * lam * W ≤ (1 + t ^ 2 * lam) * W :=
    mul_le_mul_of_nonneg_right hfactor hW
  exact hmul.trans hbound

/-- The dimensionless-to-physical covariance scaling cancels exactly in the
energy-normalized product: `(lam/a^2) * (a^2*C) = lam*C`. -/
theorem physical_energy_scaling_cancels
    (a lam C : ℝ)
    (ha : a ≠ 0) :
    (lam / a ^ 2) * (a ^ 2 * C) = lam * C := by
  field_simp [ha]

/-- Consequently any scalar energy-form budget proved in dimensionless units is
unchanged by the simultaneous operator/covariance physical rescaling. -/
theorem physical_energy_budget_transfer
    (a lam C K : ℝ)
    (ha : a ≠ 0)
    (hbudget : lam * C ≤ K) :
    (lam / a ^ 2) * (a ^ 2 * C) ≤ K := by
  rw [physical_energy_scaling_cancels a lam C ha]
  exact hbudget

#print axioms energy_multiplier_le_of_resolvent_multiplier_le
#print axioms physical_energy_scaling_cancels
#print axioms physical_energy_budget_transfer

end Millennium.YangMills.BauerschmidtConnectionFRDEnergyFormFirewall
