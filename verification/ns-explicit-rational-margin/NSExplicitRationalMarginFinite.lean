import Mathlib

namespace NSExplicitRationalMarginFinite

noncomputable def alpha0 : ℝ := 9 / 4
noncomputable def b0 : ℝ := 17 / 16
noncomputable def beta0 : ℝ := 35 / 16

/-- The chosen rational point lies strictly inside the Palasek scalar parameter window. -/
theorem parameter_window :
    1 < b0 ∧ b0 < alpha0 / 2 ∧
    2 * b0 < beta0 ∧ beta0 < alpha0 ∧
    2 < alpha0 ∧ alpha0 < 5 / 2 := by
  norm_num [alpha0, b0, beta0]

/-- Child-microcell homogenization is the smallest audited positive margin. -/
theorem homogenization_margin_exact :
    (b0 - 1) * (5 - 2 * alpha0) = 1 / 32 := by
  norm_num [alpha0, b0]

/-- Geometric room for child microcells inside a parent cell. -/
theorem geometric_room_margin_exact :
    2 * (b0 - 1) * (alpha0 - 1) = 5 / 32 := by
  norm_num [alpha0, b0]

/-- Exact number-of-cells exponent required by lower-volume tiling. -/
theorem tiling_count_exponent_exact :
    2 * (alpha0 - 1) * (b0 - 1) = 5 / 32 := by
  norm_num [alpha0, b0]

/-- The square-root tiling tax removes exactly the overconcentration surplus. -/
theorem tiled_output_exponent_exact :
    1 + b0 * (alpha0 - 1) - (alpha0 - 1) * (b0 - 1) = alpha0 := by
  norm_num [alpha0, b0]

/-- Natural localization bandwidth versus child carrier. -/
theorem divergence_margin_exact :
    b0 - 2 * (alpha0 - 1) / 3 = 11 / 48 := by
  norm_num [alpha0, b0]

/-- Conservative parent-band no-aliasing margin. -/
theorem no_alias_margin_exact :
    b0 - 1 = 1 / 16 := by
  norm_num [b0]

/-- Lower-volume tiling mesh margin. -/
theorem mesh_margin_exact :
    2 * (alpha0 - 1) * (b0 - 1) / 3 = 5 / 96 := by
  norm_num [alpha0, b0]

/-- Child stress versus parent viscosity exponent gap. -/
theorem viscosity_margin_exact :
    (2 * b0 - 1) * beta0 - 2 * (b0 - 1) * alpha0 - 2 = 23 / 128 := by
  norm_num [alpha0, b0, beta0]

/-- Child stress versus activation-time exponent gap. -/
theorem activation_time_margin_exact :
    ((b0 - 1) / b0) * ((2 * b0 + 1) * beta0 - 2 * alpha0 * b0)
      = 263 / 2176 := by
  norm_num [alpha0, b0, beta0]

/-- Modulated-Beltrami residual versus next-shell stress. -/
theorem modulation_margin_exact :
    1 / 6 + 2 * (beta0 - alpha0) * (b0 - 1) = 61 / 384 := by
  norm_num [alpha0, b0, beta0]

/-- Full low-frequency background transport margin. -/
theorem background_margin_exact :
    alpha0 - 1 + (2 * b0 - 1) * (beta0 - alpha0) = 151 / 128 := by
  norm_num [alpha0, b0, beta0]

/-- Intrinsic same-shell WKB small-parameter exponent. -/
theorem wkb_margin_exact :
    1 - 2 * (alpha0 - 1) / 3 = 1 / 6 := by
  norm_num [alpha0]

/-- Sparse separated-pair output capacity is polynomially too small. -/
theorem sparse_capacity_gap_exact :
    (2 * alpha0 - 2) - 3 * (b0 - 1) = 37 / 16 := by
  norm_num [alpha0, b0]

/-- Every audited positive scalar margin is at least the common value `1/32`. -/
theorem simultaneous_common_margin :
    (1 / 32 : ℝ) ≤ (b0 - 1) * (5 - 2 * alpha0) ∧
    (1 / 32 : ℝ) ≤ 2 * (b0 - 1) * (alpha0 - 1) ∧
    (1 / 32 : ℝ) ≤ b0 - 2 * (alpha0 - 1) / 3 ∧
    (1 / 32 : ℝ) ≤ b0 - 1 ∧
    (1 / 32 : ℝ) ≤ 2 * (alpha0 - 1) * (b0 - 1) / 3 ∧
    (1 / 32 : ℝ) ≤ (2 * b0 - 1) * beta0 - 2 * (b0 - 1) * alpha0 - 2 ∧
    (1 / 32 : ℝ) ≤ ((b0 - 1) / b0) *
      ((2 * b0 + 1) * beta0 - 2 * alpha0 * b0) ∧
    (1 / 32 : ℝ) ≤ 1 / 6 + 2 * (beta0 - alpha0) * (b0 - 1) ∧
    (1 / 32 : ℝ) ≤ alpha0 - 1 + (2 * b0 - 1) * (beta0 - alpha0) ∧
    (1 / 32 : ℝ) ≤ 1 - 2 * (alpha0 - 1) / 3 := by
  norm_num [alpha0, b0, beta0]

#print axioms parameter_window
#print axioms homogenization_margin_exact
#print axioms geometric_room_margin_exact
#print axioms tiling_count_exponent_exact
#print axioms tiled_output_exponent_exact
#print axioms divergence_margin_exact
#print axioms no_alias_margin_exact
#print axioms mesh_margin_exact
#print axioms viscosity_margin_exact
#print axioms activation_time_margin_exact
#print axioms modulation_margin_exact
#print axioms background_margin_exact
#print axioms wkb_margin_exact
#print axioms sparse_capacity_gap_exact
#print axioms simultaneous_common_margin

end NSExplicitRationalMarginFinite
