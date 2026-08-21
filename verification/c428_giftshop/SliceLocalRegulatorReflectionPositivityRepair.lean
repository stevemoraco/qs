import Mathlib

namespace Millennium.YangMills.SliceLocalRegulatorReflectionPositivityRepair

variable {Ω : Type*}

def ReflectionPositive
    (L : (Ω → ℝ) → ℝ) (θ : Ω → Ω) : Prop :=
  ∀ f : Ω → ℝ, 0 ≤ L (fun x => f (θ x) * f x)

theorem factorizedWeight_preserves
    (L : (Ω → ℝ) → ℝ) (θ : Ω → Ω)
    (hRP : ReflectionPositive L θ)
    (F G : Ω → ℝ) :
    0 ≤ L (fun x =>
      F (θ x) * F x * (G (θ x) * G x)) := by
  have h := hRP (fun x => F x * G x)
  simpa [ReflectionPositive, mul_assoc, mul_left_comm, mul_comm] using h

theorem factorizedWeight_with_fixedBoundary_preserves
    (L : (Ω → ℝ) → ℝ) (θ : Ω → Ω)
    (hRP : ReflectionPositive L θ)
    (F G H : Ω → ℝ)
    (hH : ∀ x, H (θ x) = H x) :
    0 ≤ L (fun x =>
      F (θ x) * F x *
        (G (θ x) * G x * (H x * H x))) := by
  have h := hRP (fun x => F x * G x * H x)
  simpa [ReflectionPositive, hH, mul_assoc, mul_left_comm, mul_comm] using h

theorem regulator_eq_factorized_preserves
    (L : (Ω → ℝ) → ℝ) (θ : Ω → Ω)
    (hRP : ReflectionPositive L θ)
    (F G R : Ω → ℝ)
    (hR : ∀ x, R x = G (θ x) * G x) :
    0 ≤ L (fun x => F (θ x) * F x * R x) := by
  simpa [hR, mul_assoc] using
    factorizedWeight_preserves L θ hRP F G

theorem positive_normalization_preserves
    (num Z : ℝ) (hnum : 0 ≤ num) (hZ : 0 < Z) :
    0 ≤ num / Z := by
  exact div_nonneg hnum (le_of_lt hZ)

#print axioms factorizedWeight_preserves
#print axioms factorizedWeight_with_fixedBoundary_preserves
#print axioms regulator_eq_factorized_preserves
#print axioms positive_normalization_preserves

end Millennium.YangMills.SliceLocalRegulatorReflectionPositivityRepair
