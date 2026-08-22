import Mathlib

/-!
# Navier--Stokes weak-critical-tail finite core

Honesty status: finite real-algebra bookkeeping only. This file does not
formalize the volume-to-line measure lemma, spatial analyticity, harmonic
measure, Navier--Stokes PDE theory, or any official Millennium statement.
-/

namespace MillenniumBraid
namespace NSWeakCriticalTail

/-- Polynomial form of the exact tail-to-analyticity-radius synchronization.

`threshold * scaleFactor = amplitude` encodes the intense-set threshold,
`radius * threshold ≤ K * tail` is the distribution-to-radius estimate, and
`2*K*scaleFactor*c^2*tail ≤ 1` is the small-tail gate. -/
theorem tail_radius_polynomial_budget
    (amplitude c scaleFactor K tail threshold radius : ℝ)
    (hscale : 0 ≤ scaleFactor)
    (hthreshold : threshold * scaleFactor = amplitude)
    (hradius : radius * threshold ≤ K * tail)
    (htail : 2 * K * scaleFactor * c ^ 2 * tail ≤ 1) :
    2 * c ^ 2 * amplitude * radius ≤ 1 := by
  have hfactor : 0 ≤ 2 * c ^ 2 * scaleFactor := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hradius hfactor
  calc
    2 * c ^ 2 * amplitude * radius =
        (2 * c ^ 2 * scaleFactor) * (radius * threshold) := by
      rw [← hthreshold]
      ring
    _ ≤ (2 * c ^ 2 * scaleFactor) * (K * tail) := hmul
    _ = 2 * K * scaleFactor * c ^ 2 * tail := by ring
    _ ≤ 1 := htail

/-- Division form of the same synchronization: the constructed sparse radius
lies below the analyticity radius `1/(2*c^2*amplitude)`. -/
theorem tail_radius_below_analyticity_scale
    (amplitude c scaleFactor K tail threshold radius : ℝ)
    (hamplitude : 0 < amplitude)
    (hc : 0 < c)
    (hscale : 0 ≤ scaleFactor)
    (hthreshold : threshold * scaleFactor = amplitude)
    (hradius : radius * threshold ≤ K * tail)
    (htail : 2 * K * scaleFactor * c ^ 2 * tail ≤ 1) :
    radius ≤ 1 / (2 * c ^ 2 * amplitude) := by
  have hpoly : 2 * c ^ 2 * amplitude * radius ≤ 1 :=
    tail_radius_polynomial_budget amplitude c scaleFactor K tail threshold radius
      hscale hthreshold hradius htail
  have hden : 0 < 2 * c ^ 2 * amplitude := by
    positivity
  apply (le_div_iff₀ hden).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hpoly

/-- The homogeneous smooth-denominator viscosity normalization used in the
corrected stretching epsilon-gap. -/
theorem viscosity_normalization_identity
    (nu M : ℝ) :
    nu * (nu / (nu + M)) = nu ^ 2 / (nu + M) := by
  ring

#print axioms tail_radius_polynomial_budget
#print axioms tail_radius_below_analyticity_scale
#print axioms viscosity_normalization_identity

end NSWeakCriticalTail
end MillenniumBraid
