import Mathlib

/-!
# Faizal–Shabir FRD residual-product firewall

Finite scalar firewalls for the Appendix-C / embedded Section-4 finite-range
covariance decomposition audit of arXiv:2606.19362v1.

The source uses residual factors close to the identity and then treats that
closeness as if it implied a uniform contraction of their product.  These
finite theorems record the exact logical obstruction, a source-matched two-step
schedule witness, the scalar failure of the printed one-step resolvent identity,
and the corrected scalar covariance identity for the adjoint-safe residual
orientation.

This file does not formalize the gauge-covariant lattice operator, finite-range
support, the Yang–Mills RG, Osterwalder–Schrader reconstruction, a physical mass
gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirFRDResidualProductFirewall

/-- A contraction that is within `1/2` of the identity need not be a
`1/2`-contraction. -/
theorem near_identity_does_not_imply_half_contraction :
    let r : ℝ := 3 / 4
    |r| ≤ 1 ∧ |r - 1| ≤ 1 / 2 ∧ ¬ |r| ≤ 1 / 2 := by
  norm_num

/-- The first two factors of the source-style geometric schedule
`1 - (1/4) * 4^{-j}` already violate the claimed `2^{-2}` product bound. -/
theorem source_two_step_schedule_product_gt_quarter :
    (1 - (1 / 4 : ℝ)) * (1 - (1 / 16 : ℝ)) > (1 / 2 : ℝ) ^ 2 := by
  norm_num

/-- The scalar shadow of the printed one-step identity
`G = (1-R*) G (1-R) + R* G R` fails for `A=1`, `S=1/4`, `R=1-SA`. -/
theorem printed_resolvent_identity_scalar_counterexample :
    let g : ℝ := 1
    let r : ℝ := 3 / 4
    g ≠ (1 - r) * g * (1 - r) + r * g * r := by
  norm_num

/-- Exact scalar shadow of the adjoint-safe covariance identity for
`R = 1 - S A` and `G=A^{-1}`:
`G - R G R* = 2S - S A S`. -/
theorem corrected_one_step_scalar_covariance_identity
    (a s : ℝ) (ha : a ≠ 0) :
    (1 / a) - (1 - s * a) * (1 / a) * (1 - a * s)
      = 2 * s - s * a * s := by
  field_simp [ha]
  ring

/-- A sufficient scalar positivity condition for the repaired covariance
increment `2S-SAS`. -/
theorem repaired_scalar_increment_nonnegative
    (a s : ℝ) (hs : 0 ≤ s) (has : a * s ≤ 2) :
    0 ≤ 2 * s - s * a * s := by
  have h : 0 ≤ s * (2 - a * s) :=
    mul_nonneg hs (sub_nonneg.mpr has)
  nlinarith

/-- For the explicit source-matched choice `alpha=1/4`, `b=2`, the total
geometric deletion budget is only `1/3`; this is the finite arithmetic behind
the human infinite-product lower-bound audit. -/
theorem source_geometric_total_deletion_budget :
    ((1 / 4 : ℝ) / (1 - 1 / 4)) = 1 / 3 := by
  norm_num

#print axioms near_identity_does_not_imply_half_contraction
#print axioms source_two_step_schedule_product_gt_quarter
#print axioms printed_resolvent_identity_scalar_counterexample
#print axioms corrected_one_step_scalar_covariance_identity
#print axioms repaired_scalar_increment_nonnegative
#print axioms source_geometric_total_deletion_budget

end Millennium.YangMills.FaizalShabirFRDResidualProductFirewall
