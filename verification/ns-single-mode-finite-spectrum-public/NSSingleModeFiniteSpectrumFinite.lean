import Mathlib

namespace NSSingleModeFiniteSpectrumFinite

/-!
Finite algebraic shadow of the one-mode finite-spectrum firewall.

The human theorem in `stevemoraco/RH` proves that the linearization about one
real monochromatic divergence-free background has no unstable eigenvector with
finite Fourier support.  This file deliberately does not define Fourier series,
Leray projection, shift orbits, linearized Navier--Stokes operators, or spectral
instability.  It formalizes only the load-bearing scalar and equal-shell algebra.
-/

/-- Scalar factor in the exact oriented determinant of one neighboring shift
map, after the positive norm factors have been separated. -/
noncomputable def determinantFactor
    (lambda qSq ellSq qNorm rNorm : ℝ) : ℝ :=
  lambda ^ 2 * (qSq - ellSq) / (qNorm * rNorm)

/-- A nonzero transverse drift and nonzero norm denominators force every
singular boundary map onto the equal-shell locus. -/
theorem determinant_zero_forces_equal_shell
    {lambda qSq ellSq qNorm rNorm : ℝ}
    (hlambda : lambda ≠ 0)
    (hqNorm : qNorm ≠ 0)
    (hrNorm : rNorm ≠ 0)
    (hzero : determinantFactor lambda qSq ellSq qNorm rNorm = 0) :
    qSq = ellSq := by
  unfold determinantFactor at hzero
  have hden : qNorm * rNorm ≠ 0 := mul_ne_zero hqNorm hrNorm
  field_simp [hden] at hzero
  have hlambdaSq : 0 < lambda ^ 2 := sq_pos_of_ne_zero hlambda
  nlinarith

/-- The Cauchy bound in the equal-endpoint calculation restricts the orbit gap
to at most two shift steps. -/
theorem endpoint_gap_at_most_two
    {m ellSq : ℝ}
    (_hm : 0 ≤ m)
    (hellSq : 0 < ellSq)
    (hbound : m * ellSq / 2 ≤ ellSq) :
    m ≤ 2 := by
  nlinarith

/-- Scalar shadow of the zero-drift square-zero case: a nonzero eigenvalue is
incompatible with a two-step nilpotent action. -/
theorem square_zero_scalar_eigen_zero
    {mu x y : ℂ}
    (hmu : mu ≠ 0)
    (hy : y = mu * x)
    (hzero : mu * y = 0) :
    x = 0 := by
  rw [hy] at hzero
  have hmuSq : mu * mu ≠ 0 := mul_ne_zero hmu hmu
  have hmul : (mu * mu) * x = 0 := by
    simpa [mul_assoc] using hzero
  exact (mul_eq_zero.mp hmul).resolve_left hmuSq

/-- Every surviving diagonal viscous eigenvalue is nonpositive. -/
theorem viscous_diagonal_nonpositive
    {mu nu qSq : ℝ}
    (hnu : 0 ≤ nu)
    (hqSq : 0 ≤ qSq)
    (hmu : mu = -nu * qSq) :
    mu ≤ 0 := by
  nlinarith

/-- Rational-coordinate lower boundary kernel components for
`ell=(1,1,0)`, `q=(-1,0,1)`.  The barred variables are algebraically
independent here; in the Fourier application they are complex conjugates. -/
noncomputable def lowerKernelOne (abar ebar : ℂ) : ℂ := (abar + 2 * ebar) / 3
noncomputable def lowerKernelTwo (abar ebar : ℂ) : ℂ := (ebar - 4 * abar) / 3
noncomputable def lowerKernelThree (abar ebar : ℂ) : ℂ := (2 * ebar + abar) / 3

/-- Rational-coordinate upper boundary kernel components for
`r=(0,1,1)`. -/
noncomputable def upperKernelOne (a e : ℂ) : ℂ := (4 * a - e) / 3
noncomputable def upperKernelTwo (a e : ℂ) : ℂ := (-a - 2 * e) / 3
noncomputable def upperKernelThree (a e : ℂ) : ℂ := (a + 2 * e) / 3

/-- Scalar numerator of the projected internal output in the rational
representative. -/
def internalNumerator (a abar e ebar : ℂ) : ℂ :=
  4 * a * abar - a * ebar - abar * e - 2 * e * ebar

/-- Exact first component of the projected internal equal-shell coupling. -/
theorem internal_projection_first
    (a abar e ebar : ℂ) :
    (e - a) * lowerKernelOne abar ebar + (ebar - abar) * a =
      -internalNumerator a abar e ebar / 3 := by
  unfold lowerKernelOne internalNumerator
  ring

/-- Exact second component after projection to `(0,1,1)^perp`. -/
theorem internal_projection_second
    (a abar e ebar : ℂ) :
    (((e - a) * lowerKernelTwo abar ebar + (ebar - abar) * (-a)) -
      ((e - a) * lowerKernelThree abar ebar + (ebar - abar) * e)) / 2 =
      internalNumerator a abar e ebar / 3 := by
  unfold lowerKernelTwo lowerKernelThree internalNumerator
  ring

/-- Exact third component after projection to `(0,1,1)^perp`. -/
theorem internal_projection_third
    (a abar e ebar : ℂ) :
    (((e - a) * lowerKernelThree abar ebar + (ebar - abar) * e) -
      ((e - a) * lowerKernelTwo abar ebar + (ebar - abar) * (-a))) / 2 =
      -internalNumerator a abar e ebar / 3 := by
  unfold lowerKernelTwo lowerKernelThree internalNumerator
  ring

/-- The first-minus-third component of the upper boundary kernel is exactly the
negative transverse drift. -/
theorem upper_kernel_first_minus_third
    (a e : ℂ) :
    upperKernelOne a e - upperKernelThree a e = a - e := by
  unfold upperKernelOne upperKernelThree
  ring

/-- If the transverse drift is nonzero, a pure `(-E,E,-E)` internal output can
be collinear with the upper boundary kernel only when `E=0`. -/
theorem nonzero_drift_forces_zero_internal
    {a e E k : ℂ}
    (hDrift : e - a ≠ 0)
    (hFirst : -E / 3 = k * upperKernelOne a e)
    (hThird : -E / 3 = k * upperKernelThree a e) :
    E = 0 := by
  have hEq :
      k * upperKernelOne a e = k * upperKernelThree a e :=
    hFirst.symm.trans hThird
  have hProduct : k * (a - e) = 0 := by
    calc
      k * (a - e) =
          k * (upperKernelOne a e - upperKernelThree a e) := by
            rw [upper_kernel_first_minus_third]
      _ = k * upperKernelOne a e - k * upperKernelThree a e := by ring
      _ = 0 := sub_eq_zero.mpr hEq
  have hOppositeDrift : a - e ≠ 0 := by
    intro h
    apply hDrift
    calc
      e - a = -(a - e) := by ring
      _ = 0 := by rw [h]; ring
  have hk : k = 0 :=
    (mul_eq_zero.mp hProduct).resolve_right hOppositeDrift
  rw [hk, zero_mul] at hFirst
  have hInv : (3 : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by norm_num)
  have hMul : (-E) * (3 : ℂ)⁻¹ = 0 := by
    simpa [div_eq_mul_inv] using hFirst
  have hNeg : -E = 0 :=
    (mul_eq_zero.mp hMul).resolve_right hInv
  exact neg_eq_zero.mp hNeg

/-- The same finite closure cannot support a nonzero shifted eigen-equation. -/
theorem nonzero_shifted_eigen_contradiction
    {a e E k gamma v : ℂ}
    (hDrift : e - a ≠ 0)
    (hGamma : gamma ≠ 0)
    (hv : v ≠ 0)
    (hFirst : -E / 3 = k * upperKernelOne a e)
    (hThird : -E / 3 = k * upperKernelThree a e)
    (hEigen : E = gamma * v) :
    False := by
  have hE : E = 0 :=
    nonzero_drift_forces_zero_internal hDrift hFirst hThird
  have hGammaV : gamma * v = 0 := by
    rw [← hEigen, hE]
  have hvZero : v = 0 :=
    (mul_eq_zero.mp hGammaV).resolve_left hGamma
  exact hv hvZero

#print axioms determinant_zero_forces_equal_shell
#print axioms endpoint_gap_at_most_two
#print axioms square_zero_scalar_eigen_zero
#print axioms viscous_diagonal_nonpositive
#print axioms internal_projection_first
#print axioms internal_projection_second
#print axioms internal_projection_third
#print axioms upper_kernel_first_minus_third
#print axioms nonzero_drift_forces_zero_internal
#print axioms nonzero_shifted_eigen_contradiction

end NSSingleModeFiniteSpectrumFinite
