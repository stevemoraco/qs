import Mathlib

/-!
# Finite firewall for the RSS log-spiral resonance

This file formalizes only the two-dimensional coefficient algebra behind one
angular Fourier mode of the first-order rotated self-similar operator.

For cylindrical angular mode `n`, the rotation generator acts on the
`(cos(nθ), sin(nθ))` coefficient pair by

`Rₙ(a,b) = (-n b, n a)`.

A logarithmic radial phase twist with rate `2 α n` contributes the opposite
coefficient action

`S_{α,n}(a,b) = (α n b, -α n a)`

to the half-dilation term.  Thus `α Rₙ + S_{α,n}` vanishes exactly even when
`Rₙ` is nonzero.  This is the finite algebraic shadow of the critical
`r⁻¹ cos(nθ + 2 α n log r)` resonance.

It does NOT formalize cylindrical coordinates, logarithms, trigonometric
functions, the Pineau--Vicol profile equation, divergence-free coupling,
pressure, Navier--Stokes, or a Millennium conclusion.
-/

namespace NSPVLogSpiralResonance

/-- Rotation action on one real cosine/sine coefficient pair. -/
def rotationMode (n a b : ℝ) : ℝ × ℝ :=
  (-n * b, n * a)

/-- Coefficient contribution of the logarithmic radial twist to the
half-dilation operator. -/
def logRadialTwist (alpha n a b : ℝ) : ℝ × ℝ :=
  (alpha * n * b, -(alpha * n * a))

/-- First-order RSS coefficient operator `alpha * rotation + radial twist`. -/
def firstOrderRSS (alpha n a b : ℝ) : ℝ × ℝ :=
  (alpha * (rotationMode n a b).1 + (logRadialTwist alpha n a b).1,
   alpha * (rotationMode n a b).2 + (logRadialTwist alpha n a b).2)

/-- The log-radial phase twist cancels the rotation action exactly. -/
theorem exact_logspiral_resonance
    (alpha n a b : ℝ) :
    firstOrderRSS alpha n a b = (0, 0) := by
  ext <;> simp [firstOrderRSS, rotationMode, logRadialTwist] <;> ring

/-- Squared rotational activity of a coefficient pair. -/
def rotationActivitySq (n a b : ℝ) : ℝ :=
  (rotationMode n a b).1 ^ 2 + (rotationMode n a b).2 ^ 2

/-- Squared activity of the combined first-order RSS operator. -/
def firstOrderActivitySq (alpha n a b : ℝ) : ℝ :=
  (firstOrderRSS alpha n a b).1 ^ 2 + (firstOrderRSS alpha n a b).2 ^ 2

/-- The unit cosine mode has nonzero rotation activity. -/
theorem unit_mode_rotation_activity :
    rotationActivitySq 1 1 0 = 1 := by
  norm_num [rotationActivitySq, rotationMode]

/-- The same unit mode has zero combined first-order RSS activity for every
rotation speed because the radial log-phase can resonate with it. -/
theorem unit_mode_first_order_activity_zero
    (alpha : ℝ) :
    firstOrderActivitySq alpha 1 1 0 = 0 := by
  simp [firstOrderActivitySq, exact_logspiral_resonance]

/-- No positive coercivity constant can control rotational activity by the
combined first-order RSS activity on this resonant mode. -/
theorem positive_rotation_coercivity_fails
    (alpha c : ℝ) (hc : 0 < c) :
    ¬ (c * rotationActivitySq 1 1 0 ≤
       firstOrderActivitySq alpha 1 1 0) := by
  rw [unit_mode_rotation_activity, unit_mode_first_order_activity_zero]
  nlinarith

/-- The resonant mode is genuinely nonaxisymmetric at the finite coefficient
level: its rotation vector is not zero. -/
theorem unit_mode_rotation_nonzero :
    rotationMode 1 1 0 ≠ (0, 0) := by
  norm_num [rotationMode]

#print axioms exact_logspiral_resonance
#print axioms unit_mode_rotation_activity
#print axioms unit_mode_first_order_activity_zero
#print axioms positive_rotation_coercivity_fails
#print axioms unit_mode_rotation_nonzero

end NSPVLogSpiralResonance
