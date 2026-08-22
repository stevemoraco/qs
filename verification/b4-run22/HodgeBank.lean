import Mathlib

/-!
# Hodge lane: positive local safe-block arithmetic

Over a commutative ring, this file records the exact polynomial identities
for the two-generator block
`A = (-y,x)ᵀ` and
`B = [[x²,xy],[xy,y²]]`.

The two first-derivative matrices give the alternating contraction
`(∂ₓB)(∂ᵧA) - (∂ᵧB)(∂ₓA) = (-3x,-3y)ᵀ`.
The constant matrix `V = [[0,-3],[3,0]]` sends `A` to the same vector.

These are matrix and polynomial identities only. This file does not identify
an Atiyah class, a derived boundary, a local geometric model, or a Hodge
class.
-/

namespace Millennium.Hodge.SafeBlockArithmetic

noncomputable section

variable {R : Type*} [CommRing R]

def safeA (x y : R) : Fin 2 → R :=
  ![-y, x]

def safeB (x y : R) : Matrix (Fin 2) (Fin 2) R :=
  !![x ^ 2, x * y;
     x * y, y ^ 2]

def dxA : Fin 2 → R :=
  ![0, 1]

def dyA : Fin 2 → R :=
  ![-1, 0]

def dxB (x y : R) : Matrix (Fin 2) (Fin 2) R :=
  !![2 * x, y;
     y,     0]

def dyB (x y : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, x;
     x, 2 * y]

def contractionC (x y : R) : Fin 2 → R :=
  ![-3 * x, -3 * y]

def boundaryV : Matrix (Fin 2) (Fin 2) R :=
  !![0, -3;
     3,  0]

/-- The quadratic row block composes with the Koszul column to zero. -/
theorem safeBlock_BA_zero (x y : R) :
    Matrix.mulVec (safeB x y) (safeA x y) = 0 := by
  funext i
  fin_cases i <;>
    simp [safeA, safeB, Matrix.mulVec] <;>
    ring

/-- The alternating first-derivative contraction is exactly
`(-3x,-3y)ᵀ`. -/
theorem safeBlock_derivative_contraction (x y : R) :
    Matrix.mulVec (dxB x y) dyA -
      Matrix.mulVec (dyB x y) dxA = contractionC x y := by
  funext i
  fin_cases i <;>
    simp [dxA, dyA, dxB, dyB, contractionC] <;>
    ring

/-- The displayed constant matrix sends `A` to the contraction vector. -/
theorem safeBlock_VA_eq_C (x y : R) :
    Matrix.mulVec boundaryV (safeA x y) = contractionC x y := by
  funext i
  fin_cases i <;>
    simp [boundaryV, safeA, contractionC, Matrix.mulVec]

#print axioms safeBlock_BA_zero
#print axioms safeBlock_derivative_contraction
#print axioms safeBlock_VA_eq_C

end

end Millennium.Hodge.SafeBlockArithmetic
