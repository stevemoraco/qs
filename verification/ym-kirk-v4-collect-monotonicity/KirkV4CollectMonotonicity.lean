import Mathlib

namespace Millennium.YangMills

/-- Merging two scalar coefficients under one nonnegative hull weight cannot
increase their weighted absolute budget. -/
theorem weighted_two_atom_collect_le_atomic
    (w q₁ q₂ : ℝ) (hw : 0 ≤ w) :
    w * |q₁ + q₂| ≤ w * |q₁| + w * |q₂| := by
  calc
    w * |q₁ + q₂| ≤ w * (|q₁| + |q₂|) :=
      mul_le_mul_of_nonneg_left (abs_add_le q₁ q₂) hw
    _ = w * |q₁| + w * |q₂| := by ring

/-- Two successive exact-collect merges preserve the weighted atomic budget. -/
theorem weighted_three_atom_collect_le_atomic
    (w q₁ q₂ q₃ : ℝ) (hw : 0 ≤ w) :
    w * |q₁ + q₂ + q₃| ≤
      w * |q₁| + w * |q₂| + w * |q₃| := by
  calc
    w * |q₁ + q₂ + q₃|
        = w * |(q₁ + q₂) + q₃| := by ring
    _ ≤ w * |q₁ + q₂| + w * |q₃| :=
      weighted_two_atom_collect_le_atomic w (q₁ + q₂) q₃ hw
    _ ≤ (w * |q₁| + w * |q₂|) + w * |q₃| := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right
          (weighted_two_atom_collect_le_atomic w q₁ q₂ hw) (w * |q₃|)
    _ = w * |q₁| + w * |q₂| + w * |q₃| := by ring

#print axioms weighted_two_atom_collect_le_atomic
#print axioms weighted_three_atom_collect_le_atomic

end Millennium.YangMills
