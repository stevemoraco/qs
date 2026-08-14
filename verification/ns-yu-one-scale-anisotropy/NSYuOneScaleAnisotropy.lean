import Mathlib

/-!
# Navier–Stokes Yu one-scale anisotropy firewalls

Finite real-algebra facts only.

These declarations do **not** formalize Yu's filtered Navier–Stokes estimates,
Wang–Wu's local anisotropic regularity theorem, an actual affine exterior jet,
or Navier–Stokes regularity/blow-up.  They isolate two exact interfaces used by
the accompanying research audit:

* a physical affine eigengap/work-defect estimate converts scale-exactly into a
  normalized horizontal-vorticity estimate;
* perfect alignment with an instantaneous eigendirection can still fail every
  fixed-direction criterion if that eigendirection rotates between time slices.
-/

namespace NSYuOneScaleAnisotropy

noncomputable section

/-- Scale-exact normalization of an affine spectral-work estimate.

If `gamma * horizontal ≤ defect`, where `gamma` has strain scaling, then the
normalized horizontal enstrophy `horizontal / r` is controlled by normalized
work defect `r * defect` divided by normalized gap `r^2 * gamma`.
-/
theorem normalized_horizontal_from_work_defect
    (r gamma horizontal defect : ℝ)
    (hr : 0 < r)
    (hgamma : 0 < gamma)
    (hwork : gamma * horizontal ≤ defect) :
    horizontal / r ≤ (r * defect) / (r ^ 2 * gamma) := by
  have hmul := mul_le_mul_of_nonneg_right hwork (le_of_lt hr)
  have hrg : 0 < r * gamma := mul_pos hr hgamma
  have hstep : horizontal / r ≤ defect / (r * gamma) := by
    apply (div_le_div_iff₀ hr hrg).2
    nlinarith
  calc
    horizontal / r ≤ defect / (r * gamma) := hstep
    _ = (r * defect) / (r ^ 2 * gamma) := by
      field_simp [ne_of_gt hr, ne_of_gt hgamma]
      ring

/-- Once the normalized affine gap stays positive, small normalized Rayleigh
work defect gives the exact small horizontal-vorticity currency required by a
one-scale anisotropic regularity criterion. -/
theorem normalized_gap_defect_to_horizontal_smallness
    (gapNorm defectNorm horizontalNorm eta : ℝ)
    (hgap : 0 < gapNorm)
    (hbridge : horizontalNorm ≤ defectNorm / gapNorm)
    (hdefect : defectNorm ≤ gapNorm * eta) :
    horizontalNorm ≤ eta := by
  calc
    horizontalNorm ≤ defectNorm / gapNorm := hbridge
    _ ≤ eta := by
      apply (div_le_iff₀ hgap).2
      simpa [mul_comm] using hdefect

/-- Two orthogonal instantaneous preferred directions give an exact fixed-axis
cost identity.  Interpreting `(x,y,z)` as any fixed unit direction, the two
terms are the squared perpendicular costs against `e₁` and `e₂`. -/
theorem rotating_axes_fixed_direction_cost
    (x y z : ℝ)
    (hunit : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    (1 - x ^ 2) + (1 - y ^ 2) = 1 + z ^ 2 := by
  nlinarith

/-- Consequently, even perfect instantaneous alignment on two time slices with
orthogonal preferred directions cannot make the total fixed-direction
perpendicular cost smaller than one.  Time coherence of the preferred axis is
therefore load-bearing for a fixed-axis local criterion. -/
theorem rotating_perfect_alignment_not_fixed_axis_small
    (x y z : ℝ)
    (hunit : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    1 ≤ (1 - x ^ 2) + (1 - y ^ 2) := by
  rw [rotating_axes_fixed_direction_cost x y z hunit]
  nlinarith [sq_nonneg z]

#print axioms normalized_horizontal_from_work_defect
#print axioms normalized_gap_defect_to_horizontal_smallness
#print axioms rotating_axes_fixed_direction_cost
#print axioms rotating_perfect_alignment_not_fixed_axis_small

end

end NSYuOneScaleAnisotropy
