import Mathlib

namespace B4Auto20Run3

/-- BANKER: multiplication by two on `ℤ` is injective. This is the finite algebra
model for a control map that has no kernel defect. -/
theorem bsd_double_control_injective :
    Function.Injective (fun z : ℤ => 2 * z) := by
  intro x y h
  omega

/-- CRITIC: the same injective map is not surjective; `1` is an explicit missing
class. Thus injectivity (and absence of kernel defect) does not exactify a
control comparison. -/
theorem bsd_double_control_not_surjective :
    ¬ Function.Surjective (fun z : ℤ => 2 * z) := by
  intro hsurj
  obtain ⟨z, hz⟩ := hsurj 1
  omega

/-- CLEANER: the exact image of the model control map is the even integers, so
the surviving cokernel obstruction is a parity class rather than a hidden
kernel. -/
theorem bsd_double_control_image_iff_even (y : ℤ) :
    (∃ z : ℤ, 2 * z = y) ↔ Even y := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, by ring⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    omega

#print axioms B4Auto20Run3.bsd_double_control_injective
#print axioms B4Auto20Run3.bsd_double_control_not_surjective
#print axioms B4Auto20Run3.bsd_double_control_image_iff_even

end B4Auto20Run3
