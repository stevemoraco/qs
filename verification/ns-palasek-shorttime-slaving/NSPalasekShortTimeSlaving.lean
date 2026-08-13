import Mathlib

namespace NSPalasekShortTimeSlaving

/-- The formal quasi-steady response to a constant source in
`b' + δ b = -S`. -/
def quasiSteady (δ S : ℝ) : ℝ := -S / δ

/-- The exact zero-initial-data response at time `T` to a constant source in
`b' + δ b = -S`. -/
def constantResponse (δ T S : ℝ) : ℝ :=
  -(1 - Real.exp (-(δ * T))) * S / δ

/-- Difference between the exact finite-time response and the quasi-steady
state. -/
def slavingResidual (δ T S : ℝ) : ℝ :=
  constantResponse δ T S - quasiSteady δ S

/-- The exact response is the quasi-steady state multiplied by the fraction
`1 - exp (-δT)`. -/
theorem response_fraction_identity (δ T S : ℝ) :
    constantResponse δ T S =
      (1 - Real.exp (-(δ * T))) * quasiSteady δ S := by
  simp [constantResponse, quasiSteady]
  ring

/-- Exact transient identity: starting from zero leaves the fraction
`exp (-δT)` of the quasi-steady state unresolved. -/
theorem residual_identity (δ T S : ℝ) :
    slavingResidual δ T S =
      Real.exp (-(δ * T)) * S / δ := by
  simp [slavingResidual, constantResponse, quasiSteady]
  ring

/-- Exact absolute-value version of the transient identity. -/
theorem residual_abs_identity (δ T S : ℝ) :
    |slavingResidual δ T S| =
      Real.exp (-(δ * T)) * |quasiSteady δ S| := by
  rw [residual_identity]
  have hexp : |Real.exp (-(δ * T))| = Real.exp (-(δ * T)) :=
    abs_of_pos (Real.exp_pos _)
  simp [quasiSteady, abs_div, abs_mul, hexp]
  ring

/-- If the activation clock obeys `δT ≤ η`, then the unresolved transient
fraction is at least `exp (-η)`. -/
theorem transient_fraction_lower {δ T η : ℝ}
    (hclock : δ * T ≤ η) :
    Real.exp (-η) ≤ Real.exp (-(δ * T)) := by
  exact Real.exp_le_exp.mpr (by linarith)

/-- Finite-time response cannot be close to quasi-steady on a short damping
clock. -/
theorem short_time_residual_lower {δ T η S : ℝ}
    (hclock : δ * T ≤ η) :
    Real.exp (-η) * |quasiSteady δ S| ≤
      |slavingResidual δ T S| := by
  rw [residual_abs_identity]
  exact mul_le_mul_of_nonneg_right
    (transient_fraction_lower hclock) (abs_nonneg _)

/-- A quantitative no-slaving theorem.  If `ε < exp (-η)` and `δT ≤ η`, a
nonzero quasi-steady state cannot have relative residual at most `ε`. -/
theorem short_time_not_epsilon_slaved
    {δ T η ε S : ℝ}
    (hclock : δ * T ≤ η)
    (hε : ε < Real.exp (-η))
    (hqss : quasiSteady δ S ≠ 0) :
    ¬ |slavingResidual δ T S| ≤ ε * |quasiSteady δ S| := by
  intro hslaved
  have hlower := short_time_residual_lower (S := S) hclock
  have hqssPos : 0 < |quasiSteady δ S| := abs_pos.mpr hqss
  have hstrict :
      ε * |quasiSteady δ S| <
        Real.exp (-η) * |quasiSteady δ S| :=
    mul_lt_mul_of_pos_right hε hqssPos
  have : ε * |quasiSteady δ S| < |slavingResidual δ T S| :=
    lt_of_lt_of_le hstrict hlower
  exact (not_lt_of_ge hslaved) this

/-- Palasek's viscous parameter condition gives a positive gap between the
activation exponent and the largest same-carrier viscous exponent. -/
theorem palasek_clock_beats_same_shell_viscosity
    {b β : ℝ} (hβ : 2 * b < β) :
    0 < β - 2 * b := by
  linarith

/-- Equivalent negative exponent for the damping accumulated over one
activation clock. -/
theorem palasek_accumulated_damping_exponent_negative
    {b β : ℝ} (hβ : 2 * b < β) :
    2 * b - β < 0 := by
  linarith

/-- A transparent parameter point inside the strict three-dimensional viscous
Palasek window. -/
theorem palasek_parameter_witness :
    let α : ℝ := 9 / 4
    let b : ℝ := 11 / 10
    let β : ℝ := 89 / 40
    2 < α ∧ 1 < b ∧ b < α / 2 ∧ 2 * b < β ∧ β < α ∧
      β - 2 * b = 1 / 40 := by
  norm_num

end NSPalasekShortTimeSlaving
