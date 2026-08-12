import Mathlib

/-!
# Navier--Stokes exact tensor commutator: finite algebraic cores

This file formalizes only elementary algebra behind the frozen-direction
cancellation and the exact local symbol-extension interface.

It does not formalize Fourier transforms, the Levi-Civita tensor as a geometric
object, Calderon--Zygmund operators, principal values, Biot--Savart, Lorentz or
BMO spaces, Jones extension, Navier--Stokes solutions, or the Clay theorem.
-/

namespace MillenniumBraid
namespace NSExactTensorCommutatorFinite

/-- Coordinate form of `v · (k × v) = 0`. -/
theorem frozen_cross_cancellation
    (v₁ v₂ v₃ k₁ k₂ k₃ : ℝ) :
    v₁ * (k₂ * v₃ - k₃ * v₂) +
      v₂ * (k₃ * v₁ - k₁ * v₃) +
      v₃ * (k₁ * v₂ - k₂ * v₁) = 0 := by
  ring

/-- The exact scalar multiplier contraction used in the frozen-direction
strain cancellation. -/
theorem frozen_multiplier_cancellation
    (v₁ v₂ v₃ k₁ k₂ k₃ : ℝ) :
    (v₁ * k₁ + v₂ * k₂ + v₃ * k₃) *
      (v₁ * (k₂ * v₃ - k₃ * v₂) +
       v₂ * (k₃ * v₁ - k₁ * v₃) +
       v₃ * (k₁ * v₂ - k₂ * v₁)) = 0 := by
  rw [frozen_cross_cancellation]
  ring

/-- If the raw stretching contraction splits into a commutator part and a
frozen unidirectional comparator, and the comparator vanishes, only the
commutator remains. -/
theorem frozen_comparator_subtraction
    (α comm comparator : ℝ)
    (hsplit : α = comm + comparator)
    (hcancel : comparator = 0) :
    α = comm := by
  linarith

/-- Abstract value of a commutator at one point.  The operator is deliberately
left arbitrary: locality of the symbol replacement uses equality of the two
operator inputs, not linearity. -/
def commutatorAt
    {ι R : Type*} [Ring R]
    (T : (ι → R) → ι → R)
    (b f : ι → R) (x : ι) : R :=
  T (fun y => b y * f y) x - b x * T f x

/-- If two symbols agree at the evaluation point and after multiplication by
the supported input, their commutators agree exactly at that point. -/
theorem commutatorAt_eq_of_input_eq
    {ι R : Type*} [Ring R]
    (T : (ι → R) → ι → R)
    (b b2 f : ι → R) (x : ι)
    (hprod : ∀ y, b y * f y = b2 y * f y)
    (hx : b x = b2 x) :
    commutatorAt T b f x = commutatorAt T b2 f x := by
  have hfun : (fun y => b y * f y) = (fun y => b2 y * f y) := by
    funext y
    exact hprod y
  simp [commutatorAt, hfun, hx]

/-- Support-local version of the exact extension interface. -/
theorem commutatorAt_eq_of_agree_on_support
    {ι R : Type*} [Ring R]
    (T : (ι → R) → ι → R)
    (b b2 f : ι → R) (S : Set ι) (x : ι)
    (hagree : ∀ y ∈ S, b y = b2 y)
    (hfzero : ∀ y ∉ S, f y = 0)
    (hx : b x = b2 x) :
    commutatorAt T b f x = commutatorAt T b2 f x := by
  apply commutatorAt_eq_of_input_eq T b b2 f x
  · intro y
    by_cases hy : y ∈ S
    · rw [hagree y hy]
    · rw [hfzero y hy]
      simp
  · exact hx

/-- Finite-dimensional scalar norm bookkeeping for three representative
commutator components. -/
theorem three_component_triangle (a b c : ℝ) :
    |a + b + c| ≤ |a| + |b| + |c| := by
  calc
    |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
    _ ≤ (|a| + |b|) + |c| := by
      simpa [add_comm] using add_le_add_right (abs_add_le a b) |c|
    _ = |a| + |b| + |c| := by ring

#print axioms frozen_cross_cancellation
#print axioms frozen_multiplier_cancellation
#print axioms frozen_comparator_subtraction
#print axioms commutatorAt_eq_of_input_eq
#print axioms commutatorAt_eq_of_agree_on_support
#print axioms three_component_triangle

end NSExactTensorCommutatorFinite
end MillenniumBraid
