import Mathlib

namespace NSPalasekShortTimeSlaving

noncomputable section

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

/-- Exact endpoint response to the source history
`S(s) = SFinal * exp (-g * (T-s))` in `b' + δb = -S`, with zero initial data. -/
def growingResponse (δ g T SFinal : ℝ) : ℝ :=
  -(1 - Real.exp (-((g + δ) * T))) * SFinal / (g + δ)

/-- Its multiplicative coefficient relative to the instantaneous quasi-steady
state at the endpoint. -/
def growingResponseCoefficient (δ g T : ℝ) : ℝ :=
  δ / (g + δ) * (1 - Real.exp (-((g + δ) * T)))

/-- Exact source-faithful response identity.  The growth rate enters the
resolvent denominator as `g + δ`. -/
theorem growing_response_fraction_identity
    {δ g T SFinal : ℝ}
    (hδ : δ ≠ 0) (hsum : g + δ ≠ 0) :
    growingResponse δ g T SFinal =
      growingResponseCoefficient δ g T * quasiSteady δ SFinal := by
  simp [growingResponse, growingResponseCoefficient, quasiSteady]
  field_simp [hδ, hsum]
  ring

/-- Exact residual from instantaneous quasi-steady elimination for an
exponentially growing source. -/
theorem growing_residual_identity
    {δ g T SFinal : ℝ}
    (hδ : δ ≠ 0) (hsum : g + δ ≠ 0) :
    growingResponse δ g T SFinal - quasiSteady δ SFinal =
      ((g + δ * Real.exp (-((g + δ) * T))) / (g + δ)) *
        (SFinal / δ) := by
  simp [growingResponse, quasiSteady]
  field_simp [hδ, hsum]
  ring

/-- If the source grows at least as fast as the viscous damping, the exact
response reaches at most half of the instantaneous quasi-steady coefficient.
The upper bound in fact holds for every real endpoint time. -/
theorem growing_response_coefficient_at_most_half
    {δ g T : ℝ}
    (hδ : 0 ≤ δ) (hg : δ ≤ g)
    (hsum : 0 < g + δ) :
    growingResponseCoefficient δ g T ≤ 1 / 2 := by
  have hExp : 0 ≤ Real.exp (-((g + δ) * T)) :=
    le_of_lt (Real.exp_pos _)
  have hFactor : 1 - Real.exp (-((g + δ) * T)) ≤ 1 := by
    linarith
  have hCoef : 0 ≤ δ / (g + δ) :=
    div_nonneg hδ (le_of_lt hsum)
  have hFirst :
      growingResponseCoefficient δ g T ≤ δ / (g + δ) := by
    simpa [growingResponseCoefficient] using
      mul_le_mul_of_nonneg_left hFactor hCoef
  have hHalf : δ / (g + δ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hsum]
    linarith
  exact le_trans hFirst hHalf

/-- Equivalent statement: at least half of the instantaneous quasi-steady
coefficient remains unresolved whenever `g ≥ δ`. -/
theorem growing_residual_fraction_at_least_half
    {δ g T : ℝ}
    (hδ : 0 ≤ δ) (hg : δ ≤ g)
    (hsum : 0 < g + δ) :
    1 / 2 ≤ 1 - growingResponseCoefficient δ g T := by
  have h := growing_response_coefficient_at_most_half (T := T) hδ hg hsum
  linarith

/-- Palasek's viscous parameter condition gives a positive gap between the
activation exponent and the largest same-carrier viscous exponent. -/
theorem palasek_clock_beats_same_shell_viscosity
    {b β : ℝ} (hβ : 2 * b < β) :
    0 < β - 2 * b := by
  linarith

/-- Equivalent negative exponent for the damping/growth rate ratio. -/
theorem palasek_damping_to_growth_exponent_negative
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

end

end NSPalasekShortTimeSlaving
