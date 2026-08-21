import Mathlib

/-!
# RH C484B finite B46 actual-prime tent-stencil core

This file formalizes only the load-bearing finite real-algebra identities behind
`stevemoraco/RH#2889`:

* the five-point B46 stencil;
* its reduction to a three-point curvature of centered second differences;
* the exact Laurent-polynomial factorization exposing the pole-neutral roots;
* annihilation of the two geometric exponential modes;
* the cleared-denominator floor/curvature equivalence.

It does not formalize primes, Chebyshev functions, the PNT, Stieltjes
integration, the B329/B330 explicit-formula chain, zeta zeros, BGST, or RH.
-/

namespace Millennium
namespace RH
namespace C484B

/-- The symmetric five-point coefficient row, with arguments ordered from
`t-2h` through `t+2h`. -/
def fivePoint
    (c jm2 jm1 j0 jp1 jp2 : ℝ) : ℝ :=
  -c * jp2 + (1 + c) ^ 2 * jp1
    - 2 * (1 + c + c ^ 2) * j0
    + (1 + c) ^ 2 * jm1 - c * jm2

/-- The five-point row is exactly the three-point curvature of the centered
second difference. -/
theorem fivePoint_tent_curvature
    (c jm2 jm1 j0 jp1 jp2 : ℝ) :
    fivePoint c jm2 jm1 j0 jp1 jp2 =
      (1 + c ^ 2) * (jp1 - 2 * j0 + jm1)
        - c * ((jp2 - 2 * jp1 + j0) + (j0 - 2 * jm1 + jm2)) := by
  unfold fivePoint
  ring

/-- Exact polynomial form of
`z^2 D(z)=-(z-c)(z-1)^2(cz-1)`. -/
theorem stencil_factorization (c z : ℝ) :
    -c * z ^ 4 + (1 + c) ^ 2 * z ^ 3
        - 2 * (1 + c + c ^ 2) * z ^ 2
        + (1 + c) ^ 2 * z - c =
      -(z - c) * (z - 1) ^ 2 * (c * z - 1) := by
  ring

/-- The geometric mode with shift ratio `c` is annihilated exactly. -/
theorem geometric_mode_c_annihilated (a c : ℝ) :
    fivePoint c a (a * c) (a * c ^ 2) (a * c ^ 3) (a * c ^ 4) = 0 := by
  unfold fivePoint
  ring

/-- By symmetry the reciprocal geometric mode is also annihilated, written
without division by reversing the same finite geometric string. -/
theorem geometric_mode_reciprocal_annihilated (a c : ℝ) :
    fivePoint c (a * c ^ 4) (a * c ^ 3) (a * c ^ 2) (a * c) a = 0 := by
  unfold fivePoint
  ring

/-- The one-sided floor is exactly the cleared three-scale curvature bound.
No sign assumption on `c` is needed in this cleared form. -/
theorem floor_iff_cleared_curvature
    (c jm2 jm1 j0 jp1 jp2 H Csq : ℝ) :
    0 ≤ fivePoint c jm2 jm1 j0 jp1 jp2 + H + Csq ↔
      c * ((jp2 - 2 * jp1 + j0) + (j0 - 2 * jm1 + jm2)) ≤
        (1 + c ^ 2) * (jp1 - 2 * j0 + jm1) + H + Csq := by
  rw [fivePoint_tent_curvature]
  constructor <;> intro h <;> linarith

#print axioms fivePoint_tent_curvature
#print axioms stencil_factorization
#print axioms geometric_mode_c_annihilated
#print axioms geometric_mode_reciprocal_annihilated
#print axioms floor_iff_cleared_curvature

end C484B
end RH
end Millennium
