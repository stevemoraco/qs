import Mathlib

/-!
# Yu dynamic reservoir gain — finite sharpness core

Finite real algebra only.

These theorems isolate the exact algebra behind a proposed scale-to-scale
closure of a Yu-shaped absorption inequality

  A ≤ η P + C O,

when the retained reservoir also obeys a dynamic estimate

  O ≤ α A + R.

The strict gain `C * α < 1` and independent residual control are both
load-bearing. No theorem below formalizes Yu's PDE estimates, a scale recursion,
Navier--Stokes, or any Millennium Prize statement.
-/

namespace NSYuDynamicReservoirGain

/-- Combining a Yu-shaped upper absorption estimate with a dynamic reservoir
bound leaves exactly the contraction margin `1 - C*α` and the residual `C*R`. -/
theorem aggregate_dynamic_reservoir_absorption
    {A P O R η C α : ℝ}
    (hC : 0 ≤ C)
    (hupper : A ≤ η * P + C * O)
    (hres : O ≤ α * A + R) :
    (1 - C * α) * A ≤ η * P + C * R := by
  have hCO : C * O ≤ C * (α * A + R) :=
    mul_le_mul_of_nonneg_left hres hC
  nlinarith

/-- If the dynamic reservoir has strict gain and no residual, a positive defect
must have positive diffusion payment. -/
theorem residual_free_subcritical_gain_forces_positive_diffusion
    {A P O η C α : ℝ}
    (hA : 0 < A)
    (hη : 0 < η)
    (hC : 0 ≤ C)
    (hgap : C * α < 1)
    (hupper : A ≤ η * P + C * O)
    (hres : O ≤ α * A) :
    0 < P := by
  have hcore : (1 - C * α) * A ≤ η * P := by
    have h := aggregate_dynamic_reservoir_absorption
      (A := A) (P := P) (O := O) (R := 0)
      (η := η) (C := C) (α := α) hC hupper
      (by simpa using hres)
    simpa using h
  have hleft : 0 < (1 - C * α) * A :=
    mul_pos (sub_pos.mpr hgap) hA
  have hηP : 0 < η * P := lt_of_lt_of_le hleft hcore
  nlinarith

/-- Sharp boundary countermodel: at `C*α = 1`, a persistent positive defect can
satisfy both inequalities with zero diffusion and zero residual. -/
theorem critical_dynamic_gain_allows_persistent_zero_payment :
    let A : ℝ := 1
    let P : ℝ := 0
    let O : ℝ := 1
    let R : ℝ := 0
    let η : ℝ := 1
    let C : ℝ := 1
    let α : ℝ := 1
    0 < A ∧
      A ≤ η * P + C * O ∧
      O ≤ α * A + R ∧
      (1 - C * α) * A = 0 ∧
      P = 0 ∧ R = 0 := by
  norm_num

/-- Even with strict dynamic gain, an uncontrolled residual can pay the entire
surplus while diffusion remains zero. -/
theorem subcritical_gain_can_be_paid_entirely_by_residual :
    let A : ℝ := 1
    let P : ℝ := 0
    let O : ℝ := 1
    let R : ℝ := 1 / 2
    let η : ℝ := 1
    let C : ℝ := 1
    let α : ℝ := 1 / 2
    C * α < 1 ∧
      0 < A ∧
      A ≤ η * P + C * O ∧
      O ≤ α * A + R ∧
      P = 0 := by
  norm_num

/-- Therefore strict dynamic gain alone, without a residual hypothesis, cannot
universally force positive diffusion. -/
theorem subcritical_gain_without_residual_control_does_not_force_diffusion :
    ¬ (∀ A P O R η C α : ℝ,
        0 < A → 0 < η → 0 ≤ C → C * α < 1 →
        A ≤ η * P + C * O → O ≤ α * A + R → 0 < P) := by
  intro h
  have hp := h 1 0 1 (1 / 2) 1 1 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at hp

#print axioms aggregate_dynamic_reservoir_absorption
#print axioms residual_free_subcritical_gain_forces_positive_diffusion
#print axioms critical_dynamic_gain_allows_persistent_zero_payment
#print axioms subcritical_gain_can_be_paid_entirely_by_residual
#print axioms subcritical_gain_without_residual_control_does_not_force_diffusion

end NSYuDynamicReservoirGain
