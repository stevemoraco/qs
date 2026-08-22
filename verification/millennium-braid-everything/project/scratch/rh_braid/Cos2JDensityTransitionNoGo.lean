import Mathlib

/-!
# Finite core of the RH density-transition no-go

This file formalizes only the elementary scaling implication used in
`COS2J_DENSITY_TRANSITION_NO_GO_2026-08-11.md`.

The analytic input `M*h ≳ 2R` comes from the Riemann--von Mangoldt zero count.
The inequality `M ≤ 2J` is the smoothness requirement after a degree-`M`
annihilator.  Together they force `J*h ≳ R`.
-/

namespace RHProof
namespace DensityTransition

/-- If a radius-`R` band contains enough points that `M*h ≥ 2(1-ε)R`, and
smoothness order satisfies `2J ≥ M`, then the transition scale `J*h` is
already at least `(1-ε)R`. -/
theorem transition_scale_lower_bound
    (h R M J eps : ℝ)
    (hh : 0 ≤ h)
    (hcount : 2 * (1 - eps) * R ≤ M * h)
    (hsmooth : M ≤ 2 * J) :
    (1 - eps) * R ≤ J * h := by
  have hnonneg : 0 ≤ (2 * J - M) * h :=
    mul_nonneg (sub_nonneg.mpr hsmooth) hh
  have hMh : M * h ≤ 2 * J * h := by
    nlinarith
  nlinarith

/-- No self-consistent tail onset is possible if the guaranteed tail only
begins at `c * J*h` with `c(1-ε) > 1`, while all points up to that onset are
supposed to have been annihilated already. -/
theorem no_fixed_point
    (h R M J eps c : ℝ)
    (hh : 0 ≤ h)
    (hR : 0 < R)
    (hc : 0 ≤ c)
    (hstrict : 1 < c * (1 - eps))
    (hcount : 2 * (1 - eps) * R ≤ M * h)
    (hsmooth : M ≤ 2 * J)
    (htail : c * (J * h) ≤ R) : False := by
  have hbase : (1 - eps) * R ≤ J * h :=
    transition_scale_lower_bound h R M J eps hh hcount hsmooth
  have hscale : c * ((1 - eps) * R) ≤ c * (J * h) :=
    mul_le_mul_of_nonneg_left hbase hc
  have hgap_pos : 0 < (c * (1 - eps) - 1) * R :=
    mul_pos (sub_pos.mpr hstrict) hR
  have htoo_large : R < c * ((1 - eps) * R) := by
    nlinarith
  exact (not_lt_of_ge (hscale.trans htail)) htoo_large

end DensityTransition
end RHProof
