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

def fivePoint
    (c jm2 jm1 j0 jp1 jp2 : ℝ) : ℝ :=
  -c * jp2 + (1 + c) ^ 2 * jp1
    - 2 * (1 + c + c ^ 2) * j0
    + (1 + c) ^ 2 * jm1 - c * jm2

theorem fivePoint_tent_curvature
    (c jm2 jm1 j0 jp1 jp2 : ℝ) :
    fivePoint c jm2 jm1 j0 jp1 jp2 =
      (1 + c ^ 2) * (jp1 - 2 * j0 + jm1)
        - c * ((jp2 - 2 * jp1 + j0) + (j0 - 2 * jm1 + jm2)) := by
  unfold fivePoint
  ring

theorem stencil_factorization (c z : ℝ) :
    -c * z ^ 4 + (1 + c) ^ 2 * z ^ 3
        - 2 * (1 + c + c ^ 2) * z ^ 2
        + (1 + c) ^ 2 * z - c =
      -(z - c) * (z - 1) ^ 2 * (c * z - 1) := by
  ring

theorem geometric_mode_c_annihilated (a c : ℝ) :
    fivePoint c a (a * c) (a * c ^ 2) (a * c ^ 3) (a * c ^ 4) = 0 := by
  unfold fivePoint
  ring

theorem geometric_mode_reciprocal_annihilated (a c : ℝ) :
    fivePoint c (a * c ^ 4) (a * c ^ 3) (a * c ^ 2) (a * c) a = 0 := by
  unfold fivePoint
  ring

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
