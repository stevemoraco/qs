import Mathlib

noncomputable section

/-!
# Navier--Stokes: Yu work-level core absorption algebra

This finite file isolates the scalar algebra behind the current audit of
Runlong Yu's filtered far-field route (arXiv:2606.27560v1).

At one scale, Yu's reassigned annular work is a product of a coarse-shell
quantity and the core time-profile enstrophy `Q`.  A localized curl
integration-by-parts estimate gives, at the human PDE level,

  Q^2 <= C_Q M (P + L_shell),

where `M` is the scale-invariant local energy, `P` is filtered diffusion, and
`L_shell` is the cutoff-shell filtered-enstrophy budget.  Weighted Cauchy on
the dyadic annular row gives a second scalar input

  X^2 <= 2 A2,

where `A2` is the weighted sum of squared annular reservoirs.

The theorem below proves that if `mu <= C*q*X`, these two square bounds remove
the previously isolated square-root loss *at the work level*.  After clearing
the positive denominator, the far-field work is bounded by diffusion/shell
currency plus a term linear in the squared annular reservoir currency.

This is finite real algebra only.  It does not formalize Yu's PDE theorem,
localized curl integration by parts, annular reassignment, Navier--Stokes
regularity, or blow-up.
-/

namespace NSYuWorkLevelCoreAbsorption

/-- Cleared-denominator form of the work-level Young absorption.

Assume

* `mu <= C*q*X`;
* `q^2 <= M*D` (the core profile is controlled by local energy times an
  absorbable diffusion/shell budget);
* `X^2 <= 2*A2` (the dyadic annular row is controlled by its weighted square
  currency).

Then for every positive `eta` and `M`, the exact cleared inequality is

`4*eta*M*mu <= 4*eta^2*M*D + 2*C^2*M^2*A2`.

Dividing by `4*eta*M` gives the human-readable estimate

`mu <= eta*D + (C^2*M/(2*eta))*A2`.
-/
theorem work_level_absorption_cleared
    {C M eta q X D A2 mu : ℝ}
    (hM : 0 < M)
    (heta : 0 < eta)
    (hq2 : q ^ 2 <= M * D)
    (hX2 : X ^ 2 <= 2 * A2)
    (hmu : mu <= C * q * X) :
    4 * eta * M * mu <=
      4 * eta ^ 2 * M * D + 2 * C ^ 2 * M ^ 2 * A2 := by
  have hfac : 0 <= 4 * eta * M := by positivity
  have hmu' := mul_le_mul_of_nonneg_left hmu hfac
  have hqfac : 0 <= 4 * eta ^ 2 := by positivity
  have hq2' := mul_le_mul_of_nonneg_left hq2 hqfac
  have hxfac : 0 <= C ^ 2 * M ^ 2 := by positivity
  have hX2' := mul_le_mul_of_nonneg_left hX2 hxfac
  have hsq : 0 <= (2 * eta * q - C * M * X) ^ 2 := sq_nonneg _
  nlinarith

/-- Human-readable version of `work_level_absorption_cleared`.
The square-root transition currency has disappeared: the right side is linear
in the absorbable budget `D` and linear in the squared annular currency `A2`. -/
theorem work_level_absorption
    {C M eta q X D A2 mu : ℝ}
    (hM : 0 < M)
    (heta : 0 < eta)
    (hq2 : q ^ 2 <= M * D)
    (hX2 : X ^ 2 <= 2 * A2)
    (hmu : mu <= C * q * X) :
    mu <= eta * D + (C ^ 2 * M / (2 * eta)) * A2 := by
  have hclear := work_level_absorption_cleared hM heta hq2 hX2 hmu
  have hpos : 0 < 4 * eta * M := by positivity
  have heq :
      4 * eta ^ 2 * M * D + 2 * C ^ 2 * M ^ 2 * A2 =
        (4 * eta * M) *
          (eta * D + (C ^ 2 * M / (2 * eta)) * A2) := by
    field_simp [ne_of_gt heta]
    ring
  rw [heq] at hclear
  nlinarith

/-- If the annular weighted square currency is zero, the same work-level
mechanism leaves only the arbitrarily chosen absorbable `eta*D` term. -/
theorem zero_annular_square_currency
    {C M eta q X D mu : ℝ}
    (hM : 0 < M)
    (heta : 0 < eta)
    (hq2 : q ^ 2 <= M * D)
    (hX2 : X ^ 2 <= 0)
    (hmu : mu <= C * q * X) :
    mu <= eta * D := by
  have h := work_level_absorption
    (C := C) (M := M) (eta := eta) (q := q) (X := X)
    (D := D) (A2 := 0) (mu := mu) hM heta hq2 (by simpa using hX2) hmu
  simpa using h

#print axioms work_level_absorption_cleared
#print axioms work_level_absorption
#print axioms zero_annular_square_currency

end NSYuWorkLevelCoreAbsorption
