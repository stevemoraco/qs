import Mathlib

/-!
# General symmetric equal-shell three-mode sideband no-go

Finite scalar core of the human theorem
`stevemoraco/RH@cb5c0e840efa4fc2b092e4c77803ac28df866b55`.

Interpretation external to this file:
- `A*z2 + B*z1 = 0` is the vertical condition for Leray annihilation of
  the real-conjugate high-high difference output;
- `-A*z2 + B*z1 ≠ 0` is nonvanishing of the desired high-high sum output;
- `C*z1 = 2*A*Z` and `C*z2 = 2*B*Z` are necessary vertical conditions
  for annihilation of the two principal low-high outer sidebands;
- `(C,0,Z)` is the low polarization.

The theorem proves these four conditions force the low polarization to be zero.
It formalizes no Fourier analysis, Leray projector, localization, PDE, or
Navier--Stokes theorem.
-/

namespace NSBraid
namespace GeneralThreeModeSidebandNoGo

/-- Difference-sideband cancellation plus nonzero desired output force both
in-plane high coefficients to be nonzero. -/
theorem high_coefficients_nonzero
    (A B z1 z2 : ℝ)
    (hdiff : A * z2 + B * z1 = 0)
    (hdesired : -A * z2 + B * z1 ≠ 0) :
    A ≠ 0 ∧ B ≠ 0 := by
  constructor
  · intro hA
    subst A
    simp only [zero_mul, zero_add] at hdiff
    simp only [neg_zero, zero_mul, zero_add] at hdesired
    exact hdesired hdiff
  · intro hB
    subst B
    simp only [zero_mul, add_zero] at hdiff
    simp only [zero_mul, add_zero] at hdesired
    have hz : A * z2 = 0 := hdiff
    exact hdesired (by linarith)

/-- Exact determinant identity: if both outer vertical coefficients vanish,
then the low in-plane component times the desired-output determinant vanishes. -/
theorem outer_conditions_force_determinant_product_zero
    (A B C z1 z2 Z : ℝ)
    (hout1 : C * z1 = 2 * A * Z)
    (hout2 : C * z2 = 2 * B * Z) :
    C * (B * z1 - A * z2) = 0 := by
  calc
    C * (B * z1 - A * z2)
        = B * (C * z1) - A * (C * z2) := by ring
    _ = B * (2 * A * Z) - A * (2 * B * Z) := by rw [hout1, hout2]
    _ = 0 := by ring

/-- General no-go: under exact high-high difference cancellation and nonzero
desired high-high sum forcing, simultaneous annihilation of both principal
low-high outer sidebands forces the entire low polarization `(C,0,Z)` to
vanish. No special shell aspect ratio and no nonzero hypothesis on `C` or `Z`
is assumed. -/
theorem general_single_low_sideband_nogo
    (A B C z1 z2 Z : ℝ)
    (hdiff : A * z2 + B * z1 = 0)
    (hdesired : -A * z2 + B * z1 ≠ 0)
    (hout1 : C * z1 = 2 * A * Z)
    (hout2 : C * z2 = 2 * B * Z) :
    C = 0 ∧ Z = 0 := by
  have hAB := high_coefficients_nonzero A B z1 z2 hdiff hdesired
  have hprod := outer_conditions_force_determinant_product_zero A B C z1 z2 Z hout1 hout2
  have hdet : B * z1 - A * z2 ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdesired
  have hC : C = 0 := by
    exact (mul_eq_zero.mp hprod).resolve_right hdet
  have hZ : Z = 0 := by
    rw [hC, zero_mul] at hout1
    have hA : A ≠ 0 := hAB.1
    have : A * Z = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hA
  exact ⟨hC, hZ⟩

#print axioms high_coefficients_nonzero
#print axioms outer_conditions_force_determinant_product_zero
#print axioms general_single_low_sideband_nogo

end GeneralThreeModeSidebandNoGo
end NSBraid
