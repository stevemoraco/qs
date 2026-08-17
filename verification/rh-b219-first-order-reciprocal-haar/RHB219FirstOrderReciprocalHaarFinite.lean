import Mathlib

/-!
# B219 finite first-order reciprocal-Haar algebra

Finite algebra only.

This file formalizes the load-bearing scalar identities behind the B219 human
proof:

* the two branchwise identities `psi' + psi/2 = eta`;
* the reciprocal-Haar symbol factorization;
* the balanced three-jump packet;
* the hostile intermediate-mode exponent ledger;
* the exact weighted moment simplifications used in the diagonal constant.

It does **not** formalize derivatives, integrals, prime sums, proper-power
bounds, PNT, Pringsheim--Landau, zeta, Xi, Deng--Yang--Lu, B46, RH, or not-RH.
-/

namespace RHB219FirstOrderReciprocalHaarFinite

/-- Left-branch algebra behind `psi' + psi/2 = c`. -/
theorem left_first_order (c z : ℝ) :
    z + (2 * (c - z)) / 2 = c := by
  ring

/-- Right-branch algebra behind `psi' + psi/2 = -1`. -/
theorem right_first_order (c z : ℝ) :
    -c * z + (2 * (c * z - 1)) / 2 = -1 := by
  ring

/-- Quadratic factorization of the reciprocal-Haar symbol after multiplying by
`z = exp(h*s)`. -/
theorem reciprocal_symbol_factor (c z : ℂ) :
    c * z ^ 2 - (1 + c) * z + 1 = (z - 1) * (c * z - 1) := by
  ring

/-- Every prime contributes a balanced three-jump packet. -/
theorem balanced_event_packet (c w : ℝ) :
    c * w - (1 + c) * w + w = 0 := by
  ring

/-- Exact exponent ledger for a hostile mode with real exponent
`-1/2 + delta`; squaring gives energy exponent `-1 + 2*delta`. -/
theorem hostile_energy_exponent (delta : ℝ) :
    2 * (-(1 : ℝ) / 2 + delta) = -1 + 2 * delta := by
  ring

/-- Exact scalar simplification behind the zeroth exponentially weighted
clipping moment. -/
theorem diagonal_zeroth_moment_ledger (r : ℝ) :
    ((1 : ℝ) - 1 / 2) * (2 * (r - 1)) = r - 1 := by
  ring

/-- Exact scalar simplification behind the first exponentially weighted
clipping moment. -/
theorem diagonal_first_moment_ledger (h L r : ℝ) :
    ((1 - L) / 2) * (2 * (r - 1))
        - (1 / 2) * (h * (1 + r) + 2 * (1 - r))
      = (2 - L) * (r - 1) - h * (1 + r) / 2 := by
  ring

#print axioms left_first_order
#print axioms right_first_order
#print axioms reciprocal_symbol_factor
#print axioms balanced_event_packet
#print axioms hostile_energy_exponent
#print axioms diagonal_zeroth_moment_ledger
#print axioms diagonal_first_moment_ledger

end RHB219FirstOrderReciprocalHaarFinite
