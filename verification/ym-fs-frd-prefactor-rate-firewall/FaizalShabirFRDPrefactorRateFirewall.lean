import Mathlib

/-!
# Faizal--Shabir FRD prefactor-rate firewall

Finite scalar algebra for the factor-count issue in arXiv:2606.19362v1,
Theorem 5.1, Eq. (5.12), and the repaired decay-vs-entropy ledger attempted
in Proposition 5.5.

The printed Schur estimate retains a multiplicative power of the one-kernel
prefactor `C₁` before passing to a pure exponential diameter tail. These lemmas
record that a per-factor prefactor can exactly cancel or reverse an otherwise
strict geometric decay unless its growth is paid in the final rate. They also
record that polymer-count growth, boundary-attachment growth, and kernel decay
combine into one exact net geometric base.

This file does not formalize FRD kernels, polymers, Schur operators, OS
Hilbert spaces, Yang--Mills theory, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirFRDPrefactorRateFirewall

/-- A factor growing like `2^n` exactly cancels a geometric decay `(1/2)^n`.
This is the finite shadow of an unaccounted per-polymer-factor prefactor. -/
theorem prefactor_can_exactly_cancel_geometric_decay (n : ℕ) :
    (2 : ℝ) ^ n * ((1 : ℝ) / 2) ^ n = 1 := by
  rw [← mul_pow]
  norm_num

/-- A factor growing like `2^n` can reverse the decay `(3/4)^n` into growth
`(3/2)^n`. -/
theorem prefactor_can_reverse_geometric_decay (n : ℕ) :
    (2 : ℝ) ^ n * ((3 : ℝ) / 4) ^ n = ((3 : ℝ) / 2) ^ n := by
  rw [← mul_pow]
  norm_num

/-- Per-diameter growth and per-diameter decay combine into one exact net
geometric base. Any repaired polymer tail estimate must control this product,
not the decay factor alone. -/
theorem per_diameter_growth_combines_exactly
    (C growth decay : ℝ) (n : ℕ) :
    C * growth ^ n * decay ^ n = C * (growth * decay) ^ n := by
  rw [mul_pow]
  ring

/-- Polymer-count growth, boundary-attachment growth, and FRD decay combine
into one exact geometric base. The corrected strict-tail condition is on this
full product. -/
theorem count_boundary_decay_combine_exactly
    (C countGrowth boundaryGrowth decay : ℝ) (n : ℕ) :
    C * countGrowth ^ n * boundaryGrowth ^ n * decay ^ n =
      C * (countGrowth * boundaryGrowth * decay) ^ n := by
  rw [mul_pow, mul_pow]
  ring

/-- At the critical net rate `growth * decay = 1`, the apparent exponential
decay disappears completely and the contribution stays equal to the fixed
prefactor `C`. -/
theorem critical_prefactor_erases_decay
    (C growth decay : ℝ) (n : ℕ)
    (hcrit : growth * decay = 1) :
    C * growth ^ n * decay ^ n = C := by
  rw [per_diameter_growth_combines_exactly C growth decay n, hcrit]
  simp

/-- If the net geometric base is larger than one, a positive contribution is
already amplified at one diameter step. -/
theorem supercritical_prefactor_breaks_one_step
    (C growth decay : ℝ)
    (hC : 0 < C)
    (hsuper : 1 < growth * decay) :
    C * growth ^ (1 : ℕ) * decay ^ (1 : ℕ) > C := by
  simp only [pow_one]
  calc
    C * growth * decay = C * (growth * decay) := by ring
    _ > C * 1 := mul_lt_mul_of_pos_left hsuper hC
    _ = C := by ring

/-- Even when the kernel decay base is strictly below one, count and boundary
growth can make the full rate supercritical. This concrete witness has
`decay = 3/4 < 1` but net base `(3/2)*(1)*(3/4) = 9/8 > 1`. -/
theorem decay_alone_does_not_control_full_rate :
    (3 : ℝ) / 4 < 1 ∧
      1 < ((3 : ℝ) / 2) * 1 * ((3 : ℝ) / 4) := by
  constructor <;> norm_num

#print axioms prefactor_can_exactly_cancel_geometric_decay
#print axioms prefactor_can_reverse_geometric_decay
#print axioms per_diameter_growth_combines_exactly
#print axioms count_boundary_decay_combine_exactly
#print axioms critical_prefactor_erases_decay
#print axioms supercritical_prefactor_breaks_one_step
#print axioms decay_alone_does_not_control_full_rate

end Millennium.YangMills.FaizalShabirFRDPrefactorRateFirewall
