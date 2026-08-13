import Mathlib

namespace Millennium.NavierStokes

structure PairState where
  p : ℝ
  q : ℝ

/-- Scalar component model of the exterior carrier map `(p,q) ↦ (2p+q,p+2q)`. -/
def exteriorStep (x : PairState) : PairState :=
  ⟨2*x.p + x.q, x.p + 2*x.q⟩

/-- The sum component is multiplied exactly by three. -/
theorem exterior_sum_triples (x : PairState) :
    (exteriorStep x).p + (exteriorStep x).q = 3 * (x.p + x.q) := by
  simp [exteriorStep]
  ring

/-- The difference component is exactly invariant. -/
theorem exterior_difference_fixed (x : PairState) :
    (exteriorStep x).p - (exteriorStep x).q = x.p - x.q := by
  simp [exteriorStep]
  ring

/-- One-step equality of squared lengths is preserved componentwise in the
    scalar reduction: equal quadratic data stay equal after the symmetric map. -/
theorem exterior_symmetry_preserved (p q : ℝ) :
    (2*p+q)^2 - (p+2*q)^2 = 3 * (p^2-q^2) := by
  ring

end Millennium.NavierStokes
