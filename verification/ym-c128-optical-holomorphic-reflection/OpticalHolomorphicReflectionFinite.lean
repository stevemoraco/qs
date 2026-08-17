import Mathlib

/-!
# Holomorphic reflection instead of a complex adjoint

For a real translation-invariant Fourier symbol `T`, the Hermitian adjoint on
real momentum can be represented by the holomorphic reflected transpose

`T(-z)^T`.

This is the finite algebra needed to continue a positive real-axis precision
matrix to complex momentum. The literal conjugate-transpose expression is not
itself a holomorphic formula in complex momentum.

This file formalizes only the boundary algebra. It does not formalize Fourier
analysis, analytic matrix inversion, contour shifting, Kirk's optical symbol,
Yang--Mills theory, or a Clay theorem.
-/

namespace Millennium.YangMills.OpticalHolomorphicReflectionFinite

open Complex

variable {m n : Type*}

/-- The reflected transpose is the holomorphic replacement for a real-axis
Hermitian adjoint. -/
def reflectedTranspose (T : ℂ → Matrix m n ℂ) (z : ℂ) : Matrix n m ℂ :=
  (T (-z)).transpose

/-- If a Fourier symbol has the real-kernel reflection law
`T(-x)=star(T(x))` on real momentum, then its reflected transpose agrees with
its conjugate transpose there. -/
theorem reflectedTranspose_eq_conjTranspose_on_real
    (T : ℂ → Matrix m n ℂ)
    (hreal : ∀ (x : ℝ) (i : m) (j : n),
      T (-(x : ℂ)) i j = star (T (x : ℂ) i j))
    (x : ℝ) :
    reflectedTranspose T (x : ℂ) = (T (x : ℂ)).conjTranspose := by
  ext i j
  simp [reflectedTranspose, hreal]

/-- The holomorphic precision continuation formed from a reflected transpose. -/
def reflectedPrecision
    [Fintype m]
    (T : ℂ → Matrix m n ℂ)
    (H : ℂ → Matrix m m ℂ)
    (z : ℂ) : Matrix n n ℂ :=
  reflectedTranspose T z * H z * T z

/-- On real momentum, the reflected precision is exactly the original
Hermitian quadratic-form precision. -/
theorem reflectedPrecision_eq_hermitian_on_real
    [Fintype m]
    (T : ℂ → Matrix m n ℂ)
    (H : ℂ → Matrix m m ℂ)
    (hreal : ∀ (x : ℝ) (i : m) (j : n),
      T (-(x : ℂ)) i j = star (T (x : ℂ) i j))
    (x : ℝ) :
    reflectedPrecision T H (x : ℂ) =
      (T (x : ℂ)).conjTranspose * H (x : ℂ) * T (x : ℂ) := by
  rw [reflectedPrecision, reflectedTranspose_eq_conjTranspose_on_real T hreal x]

/-- Complex conjugation fails complex linearity; this is the scalar firewall
against treating a literal adjoint as a holomorphic momentum map. -/
theorem conjugation_is_not_complex_linear :
    star (I * (1 : ℂ)) ≠ I * star (1 : ℂ) := by
  norm_num [Complex.ext_iff]

/-- A scalar reflection law gives the correct real-axis conjugate product
without inserting conjugation into the complex continuation. -/
theorem reflected_product_eq_star_product_on_real
    (t : ℂ → ℂ)
    (hreal : ∀ x : ℝ, t (-(x : ℂ)) = star (t (x : ℂ)))
    (x : ℝ) :
    t (-(x : ℂ)) * t (x : ℂ) = star (t (x : ℂ)) * t (x : ℂ) := by
  rw [hreal]

#print axioms reflectedTranspose_eq_conjTranspose_on_real
#print axioms reflectedPrecision_eq_hermitian_on_real
#print axioms conjugation_is_not_complex_linear
#print axioms reflected_product_eq_star_product_on_real

end Millennium.YangMills.OpticalHolomorphicReflectionFinite
