import Mathlib

/-!
# C409 finite quadratic slow-map comparison

This file formalizes only the normed finite consumer behind C409.

If two local slow maps have one common first-order approximation and each has
quadratic remainder, their difference is quadratic. A Lipschitz downstream map
transports the same defect. The file does not formalize derivatives, matrix
logarithms/exponentials, Faizal--Shabir or Balaban block maps, RG, or
Yang--Mills.
-/

namespace Millennium.YangMills.FaizalShabirQuadraticSlowMapComparison

variable {V W : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Two maps that are quadratically close to one common approximation are
quadratically close to each other. -/
theorem quadraticDifferenceFromCommonApproximation
    (f g linearApprox : V → W)
    (x : V) (cF cG : ℝ)
    (hF : ‖f x - linearApprox x‖ ≤ cF * ‖x‖ ^ 2)
    (hG : ‖g x - linearApprox x‖ ≤ cG * ‖x‖ ^ 2) :
    ‖f x - g x‖ ≤ (cF + cG) * ‖x‖ ^ 2 := by
  rw [show f x - g x =
      (f x - linearApprox x) - (g x - linearApprox x) by abel]
  calc
    ‖(f x - linearApprox x) - (g x - linearApprox x)‖
        ≤ ‖f x - linearApprox x‖ + ‖g x - linearApprox x‖ :=
      norm_sub_le _ _
    _ ≤ cF * ‖x‖ ^ 2 + cG * ‖x‖ ^ 2 := add_le_add hF hG
    _ = (cF + cG) * ‖x‖ ^ 2 := by ring

/-- A nonnegative Lipschitz constant transports a quadratic slow-variable
mismatch to a quadratic effective-data mismatch. -/
theorem lipschitzTransportQuadraticMismatch
    (effective : V → W)
    (x y : V) (lipschitz defect : ℝ)
    (hlip0 : 0 ≤ lipschitz)
    (hLip : ‖effective x - effective y‖ ≤ lipschitz * ‖x - y‖)
    (hdefect : ‖x - y‖ ≤ defect) :
    ‖effective x - effective y‖ ≤ lipschitz * defect := by
  exact hLip.trans (mul_le_mul_of_nonneg_left hdefect hlip0)

/-- Pointwise radius consumer: a quadratic defect remains inside the
corresponding quadratic row budget. -/
theorem quadraticRadiusBudget
    (c delta radius : ℝ)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta) (hrow : delta ≤ radius) :
    c * delta ^ 2 ≤ c * radius ^ 2 := by
  have hradius : 0 ≤ radius := le_trans hdelta hrow
  exact mul_le_mul_of_nonneg_left
    (sq_le_sq₀ hdelta hradius hrow) hc

#print axioms quadraticDifferenceFromCommonApproximation
#print axioms lipschitzTransportQuadraticMismatch
#print axioms quadraticRadiusBudget

end Millennium.YangMills.FaizalShabirQuadraticSlowMapComparison
