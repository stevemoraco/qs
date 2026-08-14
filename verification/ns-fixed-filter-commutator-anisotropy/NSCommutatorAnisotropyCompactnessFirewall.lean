import Mathlib

noncomputable section

namespace NSCommutatorAnisotropyCompactnessFirewall

def supportWeight (a : ℝ) : ℝ := 1 / a ^ 4

theorem quadraticMass_exact {a : ℝ} (ha : a ≠ 0) :
    supportWeight a * a ^ 2 = 1 / a ^ 2 := by
  unfold supportWeight
  field_simp [ha]
  ring

theorem cubicMass_exact {a : ℝ} (ha : a ≠ 0) :
    supportWeight a * a ^ 3 = 1 / a := by
  unfold supportWeight
  field_simp [ha]
  ring

theorem quarticMass_exact {a : ℝ} (ha : a ≠ 0) :
    supportWeight a * a ^ 4 = 1 := by
  unfold supportWeight
  field_simp [ha]

theorem subquartic_vs_quartic_exact {a : ℝ} (ha : a ≠ 0) :
    supportWeight a * a ^ 2 = 1 / a ^ 2 ∧
    supportWeight a * a ^ 3 = 1 / a ∧
    supportWeight a * a ^ 4 = 1 := by
  exact ⟨quadraticMass_exact ha, cubicMass_exact ha, quarticMass_exact ha⟩

theorem null_component_does_not_contribute
    {V : Type*} [AddCommGroup V]
    (work : V →+ ℝ) (dev iso : V)
    (hiso : work iso = 0) :
    work (dev + iso) = work dev := by
  rw [map_add, hiso, add_zero]

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
