import Mathlib

namespace Millennium
namespace Round217Hodge

def shear (t : ℚ) (v : ℚ × ℚ) : ℚ × ℚ :=
  (v.1 + t * v.2, v.2)

def inverseShear (t : ℚ) (v : ℚ × ℚ) : ℚ × ℚ :=
  shear (-t) v

theorem inverseShear_shear (t : ℚ) (v : ℚ × ℚ) :
    inverseShear t (shear t v) = v := by
  rcases v with ⟨x, y⟩
  simp [inverseShear, shear]
  ring

theorem shear_inverseShear (t : ℚ) (v : ℚ × ℚ) :
    shear t (inverseShear t v) = v := by
  rcases v with ⟨x, y⟩
  simp [inverseShear, shear]
  ring

theorem shear_fixed_on_filtration (t x : ℚ) :
    shear t (x, 0) = (x, 0) := by
  simp [shear]

theorem shear_same_quotient (t : ℚ) (v : ℚ × ℚ) :
    (shear t v).2 = v.2 := by
  rfl

theorem graded_data_do_not_determine_total_inverse :
    (∀ x : ℚ, shear 0 (x, 0) = shear 1 (x, 0)) ∧
      (∀ v : ℚ × ℚ, (shear 0 v).2 = (shear 1 v).2) ∧
      inverseShear 0 (0, 1) ≠ inverseShear 1 (0, 1) := by
  constructor
  · intro x
    simp [shear]
  constructor
  · intro v
    rfl
  · norm_num [inverseShear, shear]

#print axioms inverseShear_shear
#print axioms shear_inverseShear
#print axioms shear_fixed_on_filtration
#print axioms shear_same_quotient
#print axioms graded_data_do_not_determine_total_inverse

end Round217Hodge
end Millennium
