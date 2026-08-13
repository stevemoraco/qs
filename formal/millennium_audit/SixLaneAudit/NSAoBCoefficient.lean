import Mathlib

namespace SixLaneAudit.NSAOBCoefficient

noncomputable def simpleB (β r Γ dΓ dW : ℝ) : ℝ :=
  -2 * β * Γ * (dW + β * dΓ) / (r * (1 + β ^ 2 * r ^ 2))

theorem ao_b_simplification
    (β r Γ dΓ dW q Φ : ℝ)
    (hr : r ≠ 0) (hdΓ : dΓ ≠ 0) (hdW : dW ≠ 0)
    (hq : q = -dΓ / dW)
    (hΦ : Φ = 2 * Γ * dΓ / r ^ 3) :
    β * r ^ 2 * (1 - β * q) * Φ /
        (q * (1 + β ^ 2 * r ^ 2)) =
      simpleB β r Γ dΓ dW := by
  have hden : 1 + β ^ 2 * r ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (β * r)]
  rw [hq, hΦ]
  unfold simpleB
  field_simp [hr, hdΓ, hdW, hden]
  ring

theorem tangent_b_increment
    (β r Γ dΓ dW ε h : ℝ) (hr : r ≠ 0) :
    simpleB β r Γ (dΓ + β * r ^ 2 * ε * h) (dW + ε * h) -
        simpleB β r Γ dΓ dW =
      -2 * β * Γ * ε * h / r := by
  have hden : 1 + β ^ 2 * r ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (β * r)]
  unfold simpleB
  field_simp [hr, hden]
  ring

theorem ring_stress_product
    (β r Γ H s S : ℝ)
    (hβ : 0 < β) (hr : 0 < r) (hs : 0 < s)
    (hb : s ^ 2 = -2 * β * Γ * H / (r * (1 + β ^ 2 * r ^ 2)))
    (hS : S = -H / (r ^ 3 * s)) :
    Γ * S = s * (1 + β ^ 2 * r ^ 2) / (2 * β * r ^ 2) := by
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hden : 1 + β ^ 2 * r ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (β * r)]
  rw [hS]
  field_simp [hβ0, hr0, hs0, hden] at hb ⊢
  nlinarith

theorem ring_stress_product_pos
    (β r Γ H s S : ℝ)
    (hβ : 0 < β) (hr : 0 < r) (hs : 0 < s)
    (hb : s ^ 2 = -2 * β * Γ * H / (r * (1 + β ^ 2 * r ^ 2)))
    (hS : S = -H / (r ^ 3 * s)) :
    0 < Γ * S := by
  rw [ring_stress_product β r Γ H s S hβ hr hs hb hS]
  positivity

theorem generated_b_center_curvature_pos
    (s g κ c : ℝ)
    (hs : 0 < s) (hg : 0 < g) (hκ : 0 < κ) (hc : 0 < c) :
    0 < 12 * s * g * κ ^ 2 * c ^ 2 := by
  positivity

#print axioms ao_b_simplification
#print axioms tangent_b_increment
#print axioms ring_stress_product
#print axioms ring_stress_product_pos
#print axioms generated_b_center_curvature_pos

end SixLaneAudit.NSAOBCoefficient
