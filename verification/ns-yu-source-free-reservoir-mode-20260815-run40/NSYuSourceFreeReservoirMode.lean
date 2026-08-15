import Mathlib

/-!
# Yu source-free reservoir mode firewall

Finite real/finite-sum algebra only.

If a proposed dynamic reservoir estimate sources `O` only from past angular
defects plus a residual, then on a mode where the angular source is zero the
entire reservoir must be carried by the residual. Repeating a unit reservoir
across `N` finite scales therefore costs at least `N` total residual.

No theorem below formalizes Yu's PDE quantities, a Navier--Stokes solution, or
any Millennium Prize statement.
-/

namespace NSYuSourceFreeReservoirMode

/-- When the angular source vanishes, a dynamic reservoir inequality reduces to
an explicit residual lower bound. -/
theorem zero_angular_source_forces_residual_cover
    {O R α : ℝ}
    (h : O ≤ α * 0 + R) :
    O ≤ R := by
  simpa using h

/-- A persistent unit reservoir on `N` source-free scales requires at least `N`
total residual. This is the finite no-free-lunch obstruction to a universally
summable residual sourced only by angular defects. -/
theorem persistent_unit_reservoir_requires_linear_residual
    (N : ℕ) (R : Fin N → ℝ)
    (hR : ∀ k, (1 : ℝ) ≤ R k) :
    (N : ℝ) ≤ ∑ k, R k := by
  calc
    (N : ℝ) = ∑ _k : Fin N, (1 : ℝ) := by simp
    _ ≤ ∑ k, R k := by
      exact Finset.sum_le_sum fun k _hk => hR k

#print axioms zero_angular_source_forces_residual_cover
#print axioms persistent_unit_reservoir_requires_linear_residual

end NSYuSourceFreeReservoirMode
