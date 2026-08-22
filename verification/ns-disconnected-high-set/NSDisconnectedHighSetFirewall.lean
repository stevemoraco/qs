import Mathlib

/-!
# Navier--Stokes disconnected high-set firewall: finite scalar core

HONESTY BOUNDARY

This file formalizes only the exact scalar mean-deviation calculation behind
the two-component counterexample to the proposed intrinsic-gradient shortcut.
It does not formalize BMO, Sobolev/Lorentz spaces, Calderon--Zygmund operators,
vorticity, the Navier--Stokes equations, or any regularity criterion.
-/

namespace Millennium
namespace NavierStokes
namespace DisconnectedHighSetFinite

/-- A scalar mean between `-1` and `1` has total absolute deviation exactly
two from the two opposite prescribed values. -/
theorem opposite_values_exact_deviation
    (mean : ℝ) (hlo : -1 ≤ mean) (hhi : mean ≤ 1) :
    |1 - mean| + |-1 - mean| = 2 := by
  rw [abs_of_nonneg (by linarith : 0 ≤ 1 - mean)]
  rw [abs_of_nonpos (by linarith : -1 - mean ≤ 0)]
  linarith

/-- If two opposite-value slabs each occupy fraction `(1-epsilon)/2`, their
contribution to average absolute deviation is exactly `1-epsilon`, regardless
of the values on the intervening gap. -/
theorem opposite_slabs_exact_contribution
    (epsilon mean : ℝ)
    (hlo : -1 ≤ mean) (hhi : mean ≤ 1) :
    ((1 - epsilon) / 2) * |1 - mean|
      + ((1 - epsilon) / 2) * |-1 - mean|
      = 1 - epsilon := by
  rw [← mul_add]
  rw [opposite_values_exact_deviation mean hlo hhi]
  ring

/-- Any additional nonnegative contribution from the gap can only increase
the mean oscillation floor forced by the two slabs. -/
theorem opposite_slabs_force_floor
    (epsilon mean gapContribution : ℝ)
    (hlo : -1 ≤ mean) (hhi : mean ≤ 1)
    (hgap : 0 ≤ gapContribution) :
    1 - epsilon ≤
      ((1 - epsilon) / 2) * |1 - mean|
        + ((1 - epsilon) / 2) * |-1 - mean|
        + gapContribution := by
  rw [opposite_slabs_exact_contribution epsilon mean hlo hhi]
  linarith

/-- In particular, for every gap fraction below `1/5`, the exact floor is
strictly larger than `4/5`; componentwise zero gradients cannot make it small.
-/
theorem thin_gap_uniform_floor
    (epsilon mean gapContribution : ℝ)
    (hepsilon : epsilon < 1 / 5)
    (hlo : -1 ≤ mean) (hhi : mean ≤ 1)
    (hgap : 0 ≤ gapContribution) :
    4 / 5 <
      ((1 - epsilon) / 2) * |1 - mean|
        + ((1 - epsilon) / 2) * |-1 - mean|
        + gapContribution := by
  have hfloor := opposite_slabs_force_floor
    epsilon mean gapContribution hlo hhi hgap
  linarith

#print axioms opposite_values_exact_deviation
#print axioms opposite_slabs_exact_contribution
#print axioms opposite_slabs_force_floor
#print axioms thin_gap_uniform_floor

end DisconnectedHighSetFinite
end NavierStokes
end Millennium
