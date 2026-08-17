import Mathlib

namespace NSHeatScaleCovarianceFirewall

noncomputable section

/-- The relative heat coordinate attached to observation radius `r` and heat time `h`. -/
def relativeHeat (r h : ℝ) : ℝ := h / r ^ 2

/-- Parabolic diagonal scaling preserves the relative heat coordinate. -/
theorem relativeHeat_diagonal_invariant
    {r h lambda : ℝ} (hr : r ≠ 0) (hlambda : lambda ≠ 0) :
    relativeHeat (lambda * r) (lambda ^ 2 * h) = relativeHeat r h := by
  unfold relativeHeat
  field_simp [hr, hlambda]

/-- On one fixed observation window, heat time `tau * r^2` has relative coordinate `tau`. -/
theorem relativeHeat_on_ray {r tau : ℝ} (hr : r ≠ 0) :
    relativeHeat r (tau * r ^ 2) = tau := by
  unfold relativeHeat
  field_simp [hr]

/-- Fixed-window heat endpoints retain their exact relative-scale gap. -/
theorem fixedWindow_endpoint_gap
    {r a b : ℝ} (hr : r ≠ 0) :
    relativeHeat r (b * r ^ 2) - relativeHeat r (a * r ^ 2) = b - a := by
  rw [relativeHeat_on_ray (r := r) (tau := b) hr]
  rw [relativeHeat_on_ray (r := r) (tau := a) hr]

/-- Distinct relative heat scales remain distinct at every nonzero fixed radius. -/
theorem fixedWindow_endpoints_ne
    {r a b : ℝ} (hr : r ≠ 0) (hab : a ≠ b) :
    relativeHeat r (a * r ^ 2) ≠ relativeHeat r (b * r ^ 2) := by
  rw [relativeHeat_on_ray (r := r) (tau := a) hr]
  rw [relativeHeat_on_ray (r := r) (tau := b) hr]
  exact hab

/-- Every scalar profile of the relative heat coordinate is diagonally scale invariant. -/
def scaleProfile (f : ℝ → ℝ) (r h : ℝ) : ℝ := f (relativeHeat r h)

/-- Diagonal covariance allows an arbitrary profile in the invariant coordinate `h/r^2`. -/
theorem scaleProfile_diagonal_invariant
    (f : ℝ → ℝ) {r h lambda : ℝ} (hr : r ≠ 0) (hlambda : lambda ≠ 0) :
    scaleProfile f (lambda * r) (lambda ^ 2 * h) = scaleProfile f r h := by
  unfold scaleProfile
  rw [relativeHeat_diagonal_invariant (r := r) (h := h) (lambda := lambda) hr hlambda]

/-- A strictly increasing invariant profile has strictly separated fixed-window heat endpoints. -/
theorem strictlyIncreasing_profile_endpoint_growth
    {f : ℝ → ℝ} (hf : StrictMono f)
    {r a b : ℝ} (hr : r ≠ 0) (hab : a < b) :
    scaleProfile f r (a * r ^ 2) < scaleProfile f r (b * r ^ 2) := by
  unfold scaleProfile
  rw [relativeHeat_on_ray (r := r) (tau := a) hr]
  rw [relativeHeat_on_ray (r := r) (tau := b) hr]
  exact hf hab

/-- The window and heat pieces cancel only in the full diagonal generator. -/
theorem diagonal_generator_split (r h : ℝ) :
    (-2 * (h / r ^ 2)) + 2 * (h / r ^ 2) = 0 := by
  ring

#print axioms relativeHeat_diagonal_invariant
#print axioms relativeHeat_on_ray
#print axioms fixedWindow_endpoint_gap
#print axioms fixedWindow_endpoints_ne
#print axioms scaleProfile_diagonal_invariant
#print axioms strictlyIncreasing_profile_endpoint_growth
#print axioms diagonal_generator_split

end

end NSHeatScaleCovarianceFirewall
