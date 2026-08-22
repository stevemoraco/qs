import Mathlib

namespace Millennium.Hodge

def InitialSquareFactorTangentImage (p : ℝ → ℝ) : Prop :=
  ∃ q : ℝ → ℝ, ∀ x : ℝ, p x = x ^ 3 * q x

theorem squareFactorArcExpansion (x ε : ℝ) :
    (x ^ 3 + ε) ^ 2 = x ^ 6 + 2 * ε * x ^ 3 + ε ^ 2 := by
  ring

theorem firstCoefficient_mem_initialTangent :
    InitialSquareFactorTangentImage (fun x : ℝ => 2 * x ^ 3) := by
  refine ⟨fun _ => 2, ?_⟩
  intro x
  ring

theorem secondCoefficient_not_mem_initialTangent :
    ¬ InitialSquareFactorTangentImage (fun _ : ℝ => 1) := by
  rintro ⟨q, hq⟩
  have h0 := hq 0
  norm_num at h0

theorem higherCoefficient_tangent_promotion_false :
    (InitialSquareFactorTangentImage (fun x : ℝ => 2 * x ^ 3)) ∧
    ¬ InitialSquareFactorTangentImage (fun _ : ℝ => 1) := by
  exact ⟨firstCoefficient_mem_initialTangent,
    secondCoefficient_not_mem_initialTangent⟩

theorem squareFactorSecondCoefficient
    (D₀ D₁ D₂ R₀ R₁ R₂ : ℝ) :
    D₁ ^ 2 * R₀ + 2 * D₀ * D₁ * R₁ + 2 * D₀ * D₂ * R₀ + D₀ ^ 2 * R₂ =
      2 * D₀ * D₂ * R₀ + D₀ ^ 2 * R₂ + D₁ ^ 2 * R₀ + 2 * D₀ * D₁ * R₁ := by
  ring

#print axioms squareFactorArcExpansion
#print axioms firstCoefficient_mem_initialTangent
#print axioms secondCoefficient_not_mem_initialTangent
#print axioms higherCoefficient_tangent_promotion_false
#print axioms squareFactorSecondCoefficient

end Millennium.Hodge
