import Mathlib

/-!
# Stable regulator contraction versus refining lattice spacing

Finite real-algebra consumer for the repaired Faizal--Shabir regulator-identification route.
After matching all relevant/marginal local coordinates, suppose a remaining stable regulator
mismatch contracts by a factor `q` while the lattice spacing refines by a factor `b > 1`.
The dimensionless mismatch in physical-time units is `d / a`. One refinement step multiplies
that normalized mismatch by exactly `q * b`.

Thus `q * b < 1` is the strict rate regime compatible with vanishing normalized one-step debt;
`q * b = 1` is critical and preserves the normalized debt rather than making it vanish.

This file is only finite real algebra. It does not construct the stable RG subspace, prove a
Yang--Mills regulator contraction, identify AF and IR limits, perform OS reconstruction, or
prove a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirStableRegulatorRate

/-- Exact one-step normalization identity. If the raw mismatch changes from `d` to `q*d`
and the spacing from `a` to `a/b`, then mismatch divided by spacing is multiplied by `q*b`. -/
theorem normalized_refinement_ratio_exact
    (d a q b : ℝ)
    (ha : a ≠ 0)
    (hb : b ≠ 0) :
    (q * d) / (a / b) = (q * b) * (d / a) := by
  field_simp [ha, hb]
  ring

/-- At the critical rate `q*b = 1`, refinement leaves the normalized mismatch unchanged. -/
theorem critical_rate_preserves_normalized_debt
    (d a q b : ℝ)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hcrit : q * b = 1) :
    (q * d) / (a / b) = d / a := by
  rw [normalized_refinement_ratio_exact d a q b ha hb, hcrit]
  ring

/-- A strict factor bound on `q*b` transfers directly to the normalized mismatch. -/
theorem subcritical_rate_contracts_normalized_debt
    (d a q b theta : ℝ)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hnorm : 0 ≤ d / a)
    (hfactor : q * b ≤ theta) :
    (q * d) / (a / b) ≤ theta * (d / a) := by
  rw [normalized_refinement_ratio_exact d a q b ha hb]
  exact mul_le_mul_of_nonneg_right hfactor hnorm

/-- If the normalized factor is strictly below one and the current normalized mismatch is
positive, the next normalized mismatch is strictly smaller. -/
theorem strict_subcritical_rate_strictly_contracts
    (d a q b : ℝ)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hnorm : 0 < d / a)
    (hfactor : q * b < 1) :
    (q * d) / (a / b) < d / a := by
  rw [normalized_refinement_ratio_exact d a q b ha hb]
  have hmul := mul_lt_mul_of_pos_right hfactor hnorm
  simpa using hmul

/-- Exact `k`-step ratio identity for geometric refinement. -/
theorem geometric_contraction_over_spacing
    (C a0 q b : ℝ)
    (k : ℕ)
    (ha0 : a0 ≠ 0)
    (hb : b ≠ 0) :
    (C * q ^ k) / (a0 / b ^ k) = (C / a0) * (q * b) ^ k := by
  have hbk : b ^ k ≠ 0 := pow_ne_zero k hb
  field_simp [ha0, hbk]
  ring

/-- Critical geometric contraction `q*b=1` produces an `O(a_k)` raw mismatch whose
normalized mismatch is exactly constant. It therefore does not by itself give `o(a_k)`. -/
theorem critical_geometric_rate_is_not_vanishing_normalized
    (C a0 q b : ℝ)
    (k : ℕ)
    (ha0 : a0 ≠ 0)
    (hb : b ≠ 0)
    (hcrit : q * b = 1) :
    (C * q ^ k) / (a0 / b ^ k) = C / a0 := by
  rw [geometric_contraction_over_spacing C a0 q b k ha0 hb, hcrit]
  simp

#print axioms normalized_refinement_ratio_exact
#print axioms critical_rate_preserves_normalized_debt
#print axioms subcritical_rate_contracts_normalized_debt
#print axioms strict_subcritical_rate_strictly_contracts
#print axioms geometric_contraction_over_spacing
#print axioms critical_geometric_rate_is_not_vanishing_normalized

end Millennium.YangMills.FaizalShabirStableRegulatorRate
