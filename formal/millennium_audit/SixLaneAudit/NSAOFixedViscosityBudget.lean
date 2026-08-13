import Mathlib

namespace NSAOFixedViscosityBudget

/-- Axial viscous rate in the fixed-ratio fiber `α = β n`. -/
def viscousRate (ν β n : ℝ) : ℝ := ν * β ^ 2 * n ^ 2

/-- Energy growth upper rate after subtracting axial viscous coercivity. -/
def netRate (M ν β n : ℝ) : ℝ := M - viscousRate ν β n

/-- If the viscous rate exceeds the background stretching bound, the energy
exponent is strictly negative. -/
theorem net_rate_negative
    (M ν β n : ℝ) (h : M < viscousRate ν β n) :
    netRate M ν β n < 0 := by
  exact sub_neg.mpr h

/-- Avoiding the automatic-decay regime requires the scaled background
stretching to meet the viscous rate. -/
theorem scaled_background_threshold
    (A M ν β n : ℝ)
    (h : 0 ≤ A * M - viscousRate ν β n) :
    viscousRate ν β n ≤ A * M := by
  linarith

/-- Every non-decaying frequency lies below the explicit quadratic threshold. -/
theorem frequency_square_ceiling
    (M ν β n : ℝ)
    (hν : 0 < ν) (hβ : β ≠ 0)
    (h : viscousRate ν β n ≤ M) :
    n ^ 2 ≤ M / (ν * β ^ 2) := by
  have hβ2 : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hden : 0 < ν * β ^ 2 := mul_pos hν hβ2
  apply (le_div_iff₀ hden).2
  dsimp [viscousRate] at h
  nlinarith

/-- Use `s` as the square-root frequency scale, so the dissipative frequency
is proportional to `s^4`. -/
noncomputable def viscousLifetime (ν β s : ℝ) : ℝ :=
  1 / (ν * β ^ 2 * s ^ 4)

/-- Leading centered-curvature production rate. -/
def curvatureRate (a s : ℝ) : ℝ := a ^ 2 * s ^ 4

/-- Conditional leading `b`-drift rate. -/
def bDriftRate (a s : ℝ) : ℝ := a ^ 2 * s ^ 3

/-- The apparent fourth-power curvature gain cancels exactly against the
fourth-power viscous clock. -/
theorem curvature_viscous_clock_cancellation
    (a ν β s : ℝ)
    (hν : ν ≠ 0) (hβ : β ≠ 0) (hs : s ≠ 0) :
    curvatureRate a s * viscousLifetime ν β s =
      a ^ 2 / (ν * β ^ 2) := by
  unfold curvatureRate viscousLifetime
  field_simp [hν, hβ, hs]

/-- The conditional `b` drift pays one residual inverse square-root-frequency
factor over the same viscous lifetime. -/
theorem b_drift_viscous_clock_suppression
    (a ν β s : ℝ)
    (hν : ν ≠ 0) (hβ : β ≠ 0) (hs : s ≠ 0) :
    bDriftRate a s * viscousLifetime ν β s =
      a ^ 2 / (ν * β ^ 2 * s) := by
  unfold bDriftRate viscousLifetime
  field_simp [hν, hβ, hs]

/-- A nonzero amplitude deposits a strictly positive curvature budget when
viscosity is positive and the fixed axial ratio is nonzero. -/
theorem positive_curvature_budget
    (a ν β : ℝ)
    (ha : a ≠ 0) (hν : 0 < ν) (hβ : β ≠ 0) :
    0 < a ^ 2 / (ν * β ^ 2) := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  have hβ2 : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  exact div_pos ha2 (mul_pos hν hβ2)

/-- A centered negative `b` correction remains admissible whenever its finite
loss is smaller than the pre-existing positive `b`. -/
theorem positive_b_survives_subcritical_loss
    (b loss : ℝ) (h : loss < b) :
    0 < b - loss := by
  exact sub_pos.mpr h

#print axioms net_rate_negative
#print axioms scaled_background_threshold
#print axioms frequency_square_ceiling
#print axioms curvature_viscous_clock_cancellation
#print axioms b_drift_viscous_clock_suppression
#print axioms positive_curvature_budget
#print axioms positive_b_survives_subcritical_loss

end NSAOFixedViscosityBudget
