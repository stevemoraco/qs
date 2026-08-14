import Mathlib

/-!
# Yu pairwise-direction defect to line/mean-oscillation finite cores

Finite real algebra only.  These statements are intended as firewalls and
reusable inequalities for the Runlong Yu filtered-vorticity route.

They do **not** formalize Yu's PDE estimates, a BMO theorem, a singular profile,
or Navier--Stokes regularity/blow-up.
-/

namespace NSYuPairwiseToMeanOscillation

/-- In the exactly repeated-top-eigenvalue model `diag(a,a,-2a)`, every unit
vector in the top plane has the same maximal Rayleigh work `a`.  Thus stable
positive-plane geometry plus maximal work does not select a unique line. -/
theorem biaxial_plane_has_circle_of_maximizers
    (a x1 x2 : ℝ)
    (hunit : x1 ^ 2 + x2 ^ 2 = 1) :
    a * x1 ^ 2 + a * x2 ^ 2 + (-2 * a) * (0 : ℝ) ^ 2 = a := by
  nlinarith

/-- Two orthogonal directions are simultaneous maximizers of the same biaxial
trace-free strain.  This is the smallest countermodel to the shortcut
`stable positive plane + maximal work -> one distinguished line`. -/
theorem orthogonal_maximizers_do_not_select_a_line (a : ℝ) :
    (a * (1 : ℝ) ^ 2 + a * (0 : ℝ) ^ 2 + (-2 * a) * (0 : ℝ) ^ 2 = a) ∧
    (a * (0 : ℝ) ^ 2 + a * (1 : ℝ) ^ 2 + (-2 * a) * (0 : ℝ) ^ 2 = a) ∧
    ((1 : ℝ) * 0 + 0 * 1 = 0) := by
  norm_num

/-- For two unit planar directions, the oriented Euclidean direction defect
controls the squared component transverse to the anchor line.  The transverse
quantity is the planar determinant squared. -/
theorem planar_direction_difference_controls_line_defect
    (x1 x2 y1 y2 eps : ℝ)
    (hx : x1 ^ 2 + x2 ^ 2 = 1)
    (hy : y1 ^ 2 + y2 ^ 2 = 1)
    (hdiff : (x1 - y1) ^ 2 + (x2 - y2) ^ 2 ≤ eps) :
    (x1 * y2 - x2 * y1) ^ 2 ≤ eps := by
  let d : ℝ := x1 * y1 + x2 * y2
  have hcross : (x1 * y2 - x2 * y1) ^ 2 = 1 - d ^ 2 := by
    dsimp [d]
    nlinarith [hx, hy]
  have hdist : (x1 - y1) ^ 2 + (x2 - y2) ^ 2 = 2 - 2 * d := by
    dsimp [d]
    nlinarith [hx, hy]
  have hsquare : 0 ≤ (1 - d) ^ 2 := sq_nonneg (1 - d)
  rw [hcross, hdist] at hdiff ⊢
  nlinarith

/-- Exact two-point version of the standard mean-oscillation-from-pairwise-
difference inequality.  It is the finite model behind the passage from a
pairwise direction defect to a BMO-type mean oscillation. -/
theorem two_point_mean_oscillation_eq_pairwise
    (x y : ℝ) :
    |x - (x + y) / 2| + |y - (x + y) / 2| = |x - y| := by
  have hx : x - (x + y) / 2 = (x - y) / 2 := by ring
  have hy : y - (x + y) / 2 = -(x - y) / 2 := by ring
  rw [hx, hy, abs_neg]
  rw [abs_div, abs_div]
  norm_num

/-- On a high-vorticity core, Yu's magnitude weight
`|Omega(x)|^2 |Omega(y)|` dominates the uniform lower weight `Lambda^3`.
This is the scalar step needed before stripping magnitude weights from the
pairwise direction defect on a super-level set. -/
theorem high_vorticity_strips_yu_magnitude_weights
    (Lambda ax ay defect : ℝ)
    (hLambda : 0 ≤ Lambda)
    (hax : Lambda ≤ ax)
    (hay : Lambda ≤ ay)
    (hdefect : 0 ≤ defect) :
    Lambda ^ 3 * defect ≤ ax ^ 2 * ay * defect := by
  have haxnon : 0 ≤ ax := le_trans hLambda hax
  have hsqprod : 0 ≤ (ax - Lambda) * (ax + Lambda) := by
    exact mul_nonneg (sub_nonneg.mpr hax) (by linarith)
  have hsq : Lambda ^ 2 ≤ ax ^ 2 := by
    nlinarith
  have hcubic : Lambda ^ 3 ≤ ax ^ 2 * ay := by
    calc
      Lambda ^ 3 = Lambda ^ 2 * Lambda := by ring
      _ ≤ ax ^ 2 * Lambda := mul_le_mul_of_nonneg_right hsq hLambda
      _ ≤ ax ^ 2 * ay := mul_le_mul_of_nonneg_left hay (sq_nonneg ax)
  exact mul_le_mul_of_nonneg_right hcubic hdefect

#print axioms biaxial_plane_has_circle_of_maximizers
#print axioms orthogonal_maximizers_do_not_select_a_line
#print axioms planar_direction_difference_controls_line_defect
#print axioms two_point_mean_oscillation_eq_pairwise
#print axioms high_vorticity_strips_yu_magnitude_weights

end NSYuPairwiseToMeanOscillation
