import Mathlib

noncomputable section

namespace NSCommutatorAnisotropyCompactnessFirewall

/-- Scalar support weight for the concentration model.  The parameter `a`
represents amplitude and the support weight is `a^-4`. -/
def supportWeight (a : ℝ) : ℝ := 1 / a ^ 4

/-- Quadratic mass is subcritical relative to the quartic normalization. -/
theorem quadraticMass_exact {a : ℝ} (ha : a ≠ 0) :
    supportWeight a * a ^ 2 = 1 / a ^ 2 := by
  unfold supportWeight
  field_simp [ha]

/-- Cubic mass is also subcritical relative to the quartic normalization. -/
theorem cubicMass_exact {a : ℝ} (ha : a ≠ 0) :
    supportWeight a * a ^ 3 = 1 / a := by
  unfold supportWeight
  field_simp [ha]

/-- Quartic mass stays exactly one in the concentration model. -/
theorem quarticMass_exact {a : ℝ} (ha : a ≠ 0) :
    supportWeight a * a ^ 4 = 1 := by
  unfold supportWeight
  field_simp [ha]

/-- One exact bundle: lower moments decay as inverse powers of amplitude while
quartic defect remains normalized.  This is a scalar concentration model only,
not a Navier--Stokes realizability statement. -/
theorem subquartic_vs_quartic_exact {a : ℝ} (ha : a ≠ 0) :
    supportWeight a * a ^ 2 = 1 / a ^ 2 ∧
    supportWeight a * a ^ 3 = 1 / a ∧
    supportWeight a * a ^ 4 = 1 := by
  exact ⟨quadraticMass_exact ha, cubicMass_exact ha, quarticMass_exact ha⟩

/-- A linear work functional is completely blind to an additive component that
lies in its nullspace.  This is the finite algebraic analogue of discarding an
isotropic stress component after proving the relevant differential work operator
annihilates it. -/
theorem null_component_does_not_contribute
    {V : Type*} [AddCommGroup V]
    (work : V →+ ℝ) (dev iso : V)
    (hiso : work iso = 0) :
    work (dev + iso) = work dev := by
  rw [map_add, hiso, add_zero]

/-- Conversely, nonzero work cannot be carried entirely by a null component. -/
theorem nonzero_work_requires_visible_component
    {V : Type*} [AddCommGroup V]
    (work : V →+ ℝ) (dev iso : V)
    (hiso : work iso = 0)
    (hne : work (dev + iso) ≠ 0) :
    work dev ≠ 0 := by
  rw [null_component_does_not_contribute work dev iso hiso] at hne
  exact hne

#print axioms quadraticMass_exact
#print axioms cubicMass_exact
#print axioms quarticMass_exact
#print axioms subquartic_vs_quartic_exact
#print axioms null_component_does_not_contribute
#print axioms nonzero_work_requires_visible_component

end NSCommutatorAnisotropyCompactnessFirewall
