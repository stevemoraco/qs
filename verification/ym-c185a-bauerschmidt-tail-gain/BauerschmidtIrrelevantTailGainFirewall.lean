import Mathlib

/-!
# Bauerschmidt FRD irrelevant-tail gain firewall

Finite scalar consumer for the positive spectral-multiplier FRD already
source-applied to the dimensionless connection Laplacian in C184.

Bauerschmidt's multiplier estimates are available with arbitrary fixed powers
of `(1 + t^2 * lambda)`.  At power two, a nonnegative multiplier satisfying

  `(1 + t^2 * lambda)^2 * W <= C`

also satisfies

  `(t^2 * lambda)^2 * W <= C`.

This is the pointwise algebra behind a possible `T^{-2}` large-scale tail gain
after the interacting remainder supplies one extra spectral `lambda` beyond
the ordinary energy-form currency.  The analytic integration and, crucially,
the Yang--Mills theorem producing that extra spectral factor are not
formalized here.
-/

namespace Millennium.YangMills.BauerschmidtIrrelevantTailGainFirewall

/-- The second resolvent-multiplier moment controls the squared dimensionless
energy multiplier. -/
theorem squared_energy_multiplier_le_of_second_resolvent_bound
    (t lam W C : ℝ)
    (hlam : 0 ≤ lam)
    (hW : 0 ≤ W)
    (hbound : (1 + t ^ 2 * lam) ^ 2 * W ≤ C) :
    (t ^ 2 * lam) ^ 2 * W ≤ C := by
  have hx : 0 ≤ t ^ 2 * lam := mul_nonneg (sq_nonneg t) hlam
  have hsquare : (t ^ 2 * lam) ^ 2 ≤ (1 + t ^ 2 * lam) ^ 2 := by
    nlinarith
  have hmul : (t ^ 2 * lam) ^ 2 * W ≤ (1 + t ^ 2 * lam) ^ 2 * W :=
    mul_le_mul_of_nonneg_right hsquare hW
  exact hmul.trans hbound

/-- Exact scaling identity: the squared dimensionless energy factor is
`t^4 * lambda^2`. -/
theorem squared_energy_factor_identity
    (t lam : ℝ) :
    (t ^ 2 * lam) ^ 2 = t ^ 4 * lam ^ 2 := by
  ring

/-- If a scale is multiplied by `b^k`, a two-derivative tail gain has the
exact inverse-square scalar factor `b^(-2k)` when represented by reciprocal
powers. -/
theorem inverse_square_scale_identity
    (T b : ℝ)
    (k : ℕ)
    (hT : T ≠ 0)
    (hb : b ≠ 0) :
    1 / (T * b ^ k) ^ 2 = (1 / T ^ 2) * (1 / b ^ (2 * k)) := by
  field_simp [hT, hb]
  ring

#print axioms squared_energy_multiplier_le_of_second_resolvent_bound
#print axioms squared_energy_factor_identity
#print axioms inverse_square_scale_identity

end Millennium.YangMills.BauerschmidtIrrelevantTailGainFirewall
