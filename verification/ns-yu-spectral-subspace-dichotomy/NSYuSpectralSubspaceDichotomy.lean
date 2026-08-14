import Mathlib

/-!
# Yu affine-strain spectral subspace dichotomy — finite core

Finite scalar/diagonal symmetric-matrix algebra only.

This file does **not** formalize Runlong Yu's filtered Navier--Stokes estimates,
construct an exterior harmonic strain, prove a fixed/moving-shell comparison,
extract a singular profile, or prove Navier--Stokes regularity/blow-up.

The intended PDE reading is only this: for a positive trace-free affine strain,
loss of a visible top-line eigengap automatically creates a larger gap separating
the bottom eigendirection from the top two-plane.  Near-maximal Rayleigh work
then controls the vorticity component normal to that stable top plane.
-/

namespace NSYuSpectralSubspaceDichotomy

/-- A positive trace-free diagonal strain cannot lose both adjacent spectral
separations at once.  Either the top line has gap at least `lambda1 / 2`, or
the lower gap separating the top two-plane from the bottom line is strictly
larger than `2 * lambda1`. -/
theorem tracefree_positive_strain_gap_dichotomy
    (lambda1 lambda2 lambda3 : ℝ)
    (htrace : lambda1 + lambda2 + lambda3 = 0)
    (h12 : lambda2 ≤ lambda1)
    (hpos : 0 < lambda1) :
    lambda1 / 2 ≤ lambda1 - lambda2 ∨
      2 * lambda1 < lambda2 - lambda3 := by
  by_cases hgap : lambda1 / 2 ≤ lambda1 - lambda2
  · exact Or.inl hgap
  · right
    have hsmall : lambda1 - lambda2 < lambda1 / 2 := lt_of_not_ge hgap
    nlinarith [htrace]

/-- For a unit vector, near-maximal Rayleigh work controls its component in the
bottom eigendirection by the gap separating the top two-plane from that bottom
line. -/
theorem near_top_work_controls_bottom_component
    (lambda1 lambda2 lambda3 x1 x2 x3 eps : ℝ)
    (h12 : lambda2 ≤ lambda1)
    (hunit : x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = 1)
    (hdef :
      lambda1 -
          (lambda1 * x1 ^ 2 + lambda2 * x2 ^ 2 + lambda3 * x3 ^ 2) ≤ eps) :
    (lambda2 - lambda3) * x3 ^ 2 ≤ eps := by
  have hexact :
      lambda1 -
          (lambda1 * x1 ^ 2 + lambda2 * x2 ^ 2 + lambda3 * x3 ^ 2) -
          (lambda2 - lambda3) * x3 ^ 2 =
        (lambda1 - lambda2) * (x2 ^ 2 + x3 ^ 2) := by
    calc
      lambda1 -
            (lambda1 * x1 ^ 2 + lambda2 * x2 ^ 2 + lambda3 * x3 ^ 2) -
            (lambda2 - lambda3) * x3 ^ 2 =
          lambda1 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) -
            (lambda1 * x1 ^ 2 + lambda2 * x2 ^ 2 + lambda3 * x3 ^ 2) -
            (lambda2 - lambda3) * x3 ^ 2 := by rw [hunit]
      _ = (lambda1 - lambda2) * (x2 ^ 2 + x3 ^ 2) := by ring
  have hnon : 0 ≤ (lambda1 - lambda2) * (x2 ^ 2 + x3 ^ 2) := by
    positivity
  linarith

/-- Mirror of the top-line frame-freeze budget: if a perturbed bottom Rayleigh
value stays within `delta` of the reference bottom eigenvalue, then the new
bottom direction has small mass in the reference top two-plane, with denominator
the lower eigengap. -/
theorem bottom_rayleigh_perturbation_frame_budget
    (lambda1 lambda2 lambda3 y1 y2 y3 mu delta : ℝ)
    (h12 : lambda2 ≤ lambda1)
    (h23 : lambda3 ≤ lambda2)
    (hunit : y1 ^ 2 + y2 ^ 2 + y3 ^ 2 = 1)
    (hmu : mu ≤ lambda3 + delta)
    (hray :
      lambda1 * y1 ^ 2 + lambda2 * y2 ^ 2 + lambda3 * y3 ^ 2 ≤
        mu + delta) :
    (lambda2 - lambda3) * (y1 ^ 2 + y2 ^ 2) ≤ 2 * delta := by
  have hexact :
      lambda1 * y1 ^ 2 + lambda2 * y2 ^ 2 + lambda3 * y3 ^ 2 - lambda3 =
        (lambda2 - lambda3) * (y1 ^ 2 + y2 ^ 2) +
          (lambda1 - lambda2) * y1 ^ 2 := by
    calc
      lambda1 * y1 ^ 2 + lambda2 * y2 ^ 2 + lambda3 * y3 ^ 2 - lambda3 =
          lambda1 * y1 ^ 2 + lambda2 * y2 ^ 2 + lambda3 * y3 ^ 2 -
            lambda3 * (y1 ^ 2 + y2 ^ 2 + y3 ^ 2) := by rw [hunit]
      _ = (lambda2 - lambda3) * (y1 ^ 2 + y2 ^ 2) +
          (lambda1 - lambda2) * y1 ^ 2 := by ring
  have hnon : 0 ≤ (lambda1 - lambda2) * y1 ^ 2 := by positivity
  linarith

/-- In the small-top-gap branch of a positive trace-free strain, near-maximal
Rayleigh work forces the bottom component below the scale set by the top
eigenvalue itself. -/
theorem small_top_gap_forces_positive_plane_alignment
    (lambda1 lambda2 lambda3 x1 x2 x3 eps : ℝ)
    (htrace : lambda1 + lambda2 + lambda3 = 0)
    (h12 : lambda2 ≤ lambda1)
    (hpos : 0 < lambda1)
    (hsmall : lambda1 - lambda2 < lambda1 / 2)
    (hunit : x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = 1)
    (hdef :
      lambda1 -
          (lambda1 * x1 ^ 2 + lambda2 * x2 ^ 2 + lambda3 * x3 ^ 2) ≤ eps) :
    2 * lambda1 * x3 ^ 2 ≤ eps := by
  have hgap : 2 * lambda1 < lambda2 - lambda3 := by
    nlinarith [htrace]
  have hplane : (lambda2 - lambda3) * x3 ^ 2 ≤ eps :=
    near_top_work_controls_bottom_component
      lambda1 lambda2 lambda3 x1 x2 x3 eps h12 hunit hdef
  nlinarith [sq_nonneg x3]

#print axioms tracefree_positive_strain_gap_dichotomy
#print axioms near_top_work_controls_bottom_component
#print axioms bottom_rayleigh_perturbation_frame_budget
#print axioms small_top_gap_forces_positive_plane_alignment

end NSYuSpectralSubspaceDichotomy
