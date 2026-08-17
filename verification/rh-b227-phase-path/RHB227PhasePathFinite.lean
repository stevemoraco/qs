import Mathlib

/-!
# B227 finite phase-path algebra

Finite scalar algebra only.

This file formalizes the load-bearing identities behind the B227 aligned
phase-path consumer:

* the B226A three-point stencil is one first difference after the fixed
  preconditioner `u_k = c*m_k - m_(k-M)`;
* a critically shifted signed edge inequality is exactly monotonicity after
  the affine phase tilt;
* the four phase edges telescope to the endpoint difference;
* endpoint cancellation can coexist with nonzero alternating edges.

It does **not** formalize bounded-variation quadrature, prime sums, PNT,
Pringsheim--Landau, zeta, Xi, Deng--Yang--Lu, B46, RH, or not-RH.
-/

namespace RHB227PhasePathFinite

/-- The aligned reciprocal-Haar three-point stencil becomes one first
phase difference after the fixed preconditioner. -/
theorem phase_precondition_factor (c mPrev m mNext : ℝ) :
    (c * mNext - m) - (c * m - mPrev) =
      c * mNext - (1 + c) * m + mPrev := by
  ring

/-- A signed edge ceiling by `tau` is exactly monotonicity after subtracting
one additional copy of the affine phase tilt.  The variable `q` is the
current phase coordinate written in real scalar form. -/
theorem shifted_edge_iff_tilted_monotone
    (sigma u0 u1 tau q : ℝ) :
    sigma * (u1 - u0) ≤ tau ↔
      sigma * u1 - (q + 1) * tau ≤ sigma * u0 - q * tau := by
  constructor <;> intro h <;> linarith

/-- Four consecutive phase edges telescope exactly to the phase endpoint
difference.  B227's hostile pass uses the converse failure: the endpoint can
vanish while the individual signed edges remain nonzero. -/
theorem phase_four_edge_telescoping (u0 u1 u2 u3 u4 : ℝ) :
    (u1 - u0) + (u2 - u1) + (u3 - u2) + (u4 - u3) = u4 - u0 := by
  ring

/-- Exact alternating-edge witness showing that zero net endpoint drift does
not force the local phase edges to vanish. -/
theorem alternating_edges_endpoint_zero :
    (1 : ℝ) + (-1) + 1 + (-1) = 0 := by
  norm_num

/-- The same witness has strictly positive one-sided edge mass. -/
theorem alternating_edges_positive_mass :
    max (1 : ℝ) 0 + max (-1 : ℝ) 0 + max (1 : ℝ) 0 + max (-1 : ℝ) 0 = 2 := by
  norm_num

#print axioms phase_precondition_factor
#print axioms shifted_edge_iff_tilted_monotone
#print axioms phase_four_edge_telescoping
#print axioms alternating_edges_endpoint_zero
#print axioms alternating_edges_positive_mass

end RHB227PhasePathFinite
