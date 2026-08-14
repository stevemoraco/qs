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
  calc
    a * x1 ^ 2 + a * x2 ^ 2 + (-2 * a) * (0 : ℝ) ^ 2 =
        a * (x1 ^ 2 + x2 ^ 2) := by ring
    _ = a := by rw [hunit]; ring

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
    calc
      (x1 * y2 - x2 * y1) ^ 2 =
          (x1 ^ 2 + x2 ^ 2) * (y1 ^ 2 + y2 ^ 2) - d ^ 2 := by
            dsimp [d]
            ring
      _ = 1 - d ^ 2 := by rw [hx, hy]; ring
  have hdist : (x1 - y1) ^ 2 + (x2 - y2) ^ 2 = 2 - 2 * d := by
    calc
      (x1 - y1) ^ 2 + (x2 - y2) ^ 2 =
          (x1 ^ 2 + x2 ^ 2) + (y1 ^ 2 + y2 ^ 2) - 2 * d := by
            dsimp [d]
            ring
      _ = 2 - 2 * d := by rw [hx, hy]; ring
  have hgeom : 1 - d ^ 2 ≤ 2 - 2 * d := by
    nlinarith [sq_nonneg (1 - d)]
  calc
    (x1 * y2 - x2 * y1) ^ 2 = 1 - d ^ 2 := hcross
    _ ≤ 2 - 2 * d := hgeom
    _ = (x1 - y1) ^ 2 + (x2 - y2) ^ 2 := hdist.symm
    _ ≤ eps := hdiff

/-- Exact two-point version of the standard mean-oscillation-from-pairwise-
difference inequality.  It is the finite model behind the passage from a
pairwise direction defect to a BMO-type mean oscillation. -/
theorem two_point_mean_oscillation_eq_pairwise
    (x y : ℝ) :
    |x - (x + y) / 2| + |y - (x + y) / 2| = |x - y| := by
  have hx : x - (x + y) / 2 = (x - y) / 2 := by ring
  have hy : y - (x + y) / 2 = -(x - y) / 2 := by ring
  have htwo : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  rw [hx, hy, abs_div, abs_div, abs_neg, htwo]
  ring

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
  have hsq : Lambda ^ 2 ≤ ax ^ 2 := by
    nlinarith [sq_nonneg (ax - Lambda), hLambda, hax]
  have hcubic : Lambda ^ 3 ≤ ax ^ 2 * ay := by
    calc
      Lambda ^ 3 = Lambda ^ 2 * Lambda := by ring
      _ ≤ ax ^ 2 * Lambda := mul_le_mul_of_nonneg_right hsq hLambda
      _ ≤ ax ^ 2 * ay := mul_le_mul_of_nonneg_left hay (sq_nonneg ax)
  exact mul_le_mul_of_nonneg_right hcubic hdefect

/-- Quantitative inversion of the previous weight stripping: on a strictly
positive high-vorticity core, a small weighted angular defect forces the raw
direction defect to be small by `Lambda^{-3}`. -/
theorem weighted_defect_controls_raw_direction
    (Lambda ax ay defect eps : ℝ)
    (hLambda : 0 < Lambda)
    (hax : Lambda ≤ ax)
    (hay : Lambda ≤ ay)
    (hdefect : 0 ≤ defect)
    (hweighted : ax ^ 2 * ay * defect ≤ eps) :
    defect ≤ eps / Lambda ^ 3 := by
  have hstrip : Lambda ^ 3 * defect ≤ ax ^ 2 * ay * defect :=
    high_vorticity_strips_yu_magnitude_weights
      Lambda ax ay defect (le_of_lt hLambda) hax hay hdefect
  have hbound : Lambda ^ 3 * defect ≤ eps := le_trans hstrip hweighted
  have hcubepos : 0 < Lambda ^ 3 := pow_pos hLambda 3
  exact (le_div_iff₀ hcubepos).2 (by simpa [mul_comm] using hbound)

/-- Scalar core of the filtered-peak coverage argument.  If a peak is at least
`2*Lambda`, the Lipschitz loss across a radius `s` is at most `Lambda`, and a
point lies within that radius, then the value at that point remains at least
`Lambda`.  In the PDE application `peak` and `value` are vorticity magnitudes
and `L` is a bound for `|∇Omega_ell|`. -/
theorem high_peak_plus_lipschitz_yields_core
    (Lambda peak L s d value : ℝ)
    (hpeak : 2 * Lambda ≤ peak)
    (hL : 0 ≤ L)
    (hds : d ≤ s)
    (hLs : L * s ≤ Lambda)
    (hlower : peak - L * d ≤ value) :
    Lambda ≤ value := by
  have hLd : L * d ≤ L * s := mul_le_mul_of_nonneg_left hds hL
  linarith

/-- Converse firewall: if a point within radius `s` drops below `Lambda` despite
a `2*Lambda` peak and the lower Lipschitz estimate, then the Lipschitz loss
must exceed `Lambda`.  Thus failure of high-vorticity coverage has a visible
gradient cost. -/
theorem loss_of_high_core_forces_large_lipschitz_budget
    (Lambda peak L s d value : ℝ)
    (hpeak : 2 * Lambda ≤ peak)
    (hL : 0 ≤ L)
    (hds : d ≤ s)
    (hlower : peak - L * d ≤ value)
    (hlow : value < Lambda) :
    Lambda < L * s := by
  have hLd : L * d ≤ L * s := mul_le_mul_of_nonneg_left hds hL
  linarith

#print axioms biaxial_plane_has_circle_of_maximizers
#print axioms orthogonal_maximizers_do_not_select_a_line
#print axioms planar_direction_difference_controls_line_defect
#print axioms two_point_mean_oscillation_eq_pairwise
#print axioms high_vorticity_strips_yu_magnitude_weights
#print axioms weighted_defect_controls_raw_direction
#print axioms high_peak_plus_lipschitz_yields_core
#print axioms loss_of_high_core_forces_large_lipschitz_budget

end NSYuPairwiseToMeanOscillation
