import Mathlib

/-!
# Faizal–Shabir O(4) Riemann-normalization firewall

Finite arithmetic shadow of the Appendix Proposition 4.6 source audit.

The source displays a four-dimensional lattice-to-continuum comparison with a
factor `a⁻⁴`, followed by a continuum integral estimate of order `a`. Their
product is `a⁻³`, not `a`.  This file formalizes only that normalization
arithmetic and a dyadic witness.

It does not formalize lattice Yang–Mills, Schwinger functions, O(4) restoration,
Osterwalder–Schrader reconstruction, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirO4RiemannNormalizationFirewall

/-- A four-dimensional Riemann counting factor `a⁻⁴` times an `O(a)` integral
has scalar scale `a⁻³`. -/
theorem four_dimensional_count_times_linear_integral
    (a : ℝ) (ha : a ≠ 0) :
    (1 / a ^ 4) * a = 1 / a ^ 3 := by
  field_simp

/-- At `a = 1/2`, the displayed `a⁻⁴ * a` ledger equals `8`, not `1/2`. -/
theorem dyadic_normalization_witness :
    (1 / ((1 / 2 : ℝ) ^ 4)) * (1 / 2 : ℝ) = 8 := by
  norm_num

/-- The same dyadic ledger is therefore not the claimed linear scale `a`. -/
theorem dyadic_ledger_not_linear :
    (1 / ((1 / 2 : ℝ) ^ 4)) * (1 / 2 : ℝ) ≠ (1 / 2 : ℝ) := by
  norm_num

#print axioms four_dimensional_count_times_linear_integral
#print axioms dyadic_normalization_witness
#print axioms dyadic_ledger_not_linear

end Millennium.YangMills.FaizalShabirO4RiemannNormalizationFirewall
