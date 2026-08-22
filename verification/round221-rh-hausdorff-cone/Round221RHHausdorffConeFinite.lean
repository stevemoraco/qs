import Mathlib

/-!
# Round 221 RH Hausdorff-cone finite cores

This file formalizes only scalar inequalities used in the bounded-slope
countermodel. It does not formalize beta integrals, hyperbolic power-series
bounds, Suzuki's transforms, the xi function, zeta zeros, the triangular-ray
criterion, or the Riemann hypothesis.
-/

namespace Millennium
namespace Round221RH

/-- The explicit coefficient in the analytic countermodel. -/
def coneEta (C : ℝ) : ℝ :=
  1 / (2 * (C + 4) * (C + 5))

/-- The real-axis analytic countermodel used in the prose theorem. -/
def coneModel (C a : ℝ) : ℝ :=
  a ^ 2 - coneEta C * (Real.cosh a - 1)

/-- Under the bounded-slope hypothesis, the beta mean is uniformly separated
from zero. This is the scalar form of
`(n+1)/(n+r+4) >= 1/(C+4)`. -/
theorem cone_beta_mean_lower_bound
    (C k r : ℝ)
    (hC : 0 ≤ C) (hk : 0 < k) (hr : 0 ≤ r)
    (hcone : r ≤ C * k) :
    1 / (C + 4) ≤ k / (k + r + 3) := by
  have hleft : 0 < C + 4 := by linarith
  have hright : 0 < k + r + 3 := by linarith
  rw [div_le_div_iff₀ hleft hright]
  nlinarith

/-- If a random variable lies in `[0,1]`, has mean at least `b`, and `p` is
an upper bound for the mass above `b/2` in the elementary split estimate,
then `p >= b/2`. The probability-space layer is intentionally external. -/
theorem bounded_mean_forces_half_mass
    (b mean p : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hp0 : 0 ≤ p)
    (hmean : b ≤ mean)
    (hsplit : mean ≤ p + (1 - p) * (b / 2)) :
    b / 2 ≤ p := by
  have hpb : 0 ≤ p * b := mul_nonneg hp0 hb0
  have hcap : p * (1 - b / 2) ≤ p := by
    nlinarith
  nlinarith

/-- The model coefficient is positive for every nonnegative cone slope. -/
theorem coneEta_pos (C : ℝ) (hC : 0 ≤ C) :
    0 < coneEta C := by
  unfold coneEta
  positivity

/-- The response margin in the human proof is exactly twice the subtraction
coefficient. -/
theorem cone_response_margin_identity
    (C : ℝ) (hC : 0 ≤ C) :
    2 * coneEta C = 1 / ((C + 4) * (C + 5)) := by
  have h4 : C + 4 ≠ 0 := by linarith
  have h5 : C + 5 ≠ 0 := by linarith
  unfold coneEta
  field_simp [h4, h5]
  ring

/-- A strict factor-two response floor leaves a strict positive margin after
subtracting one copy of the adverse response. -/
theorem half_margin_subtraction
    (G H eta : ℝ)
    (hH : 0 < H) (heta : 0 ≤ eta)
    (hG : 2 * eta * H < G) :
    0 < G - eta * H := by
  have hetaH : 0 ≤ eta * H :=
    mul_nonneg heta (le_of_lt hH)
  nlinarith

/-- The analytic countermodel is even. -/
theorem coneModel_even (C a : ℝ) :
    coneModel C (-a) = coneModel C a := by
  simp [coneModel, Real.cosh_neg]

/-- The analytic countermodel has the required value-zero boundary condition. -/
theorem coneModel_zero (C : ℝ) :
    coneModel C 0 = 0 := by
  simp [coneModel]

/-- At the explicit point `a=8(C+5)`, the quartic lower shadow for `cosh-1`
already dominates the quadratic term. -/
theorem explicit_negative_quartic_shadow
    (C : ℝ) (hC : 0 ≤ C) :
    let a := 8 * (C + 5)
    let eta := coneEta C
    a ^ 2 - eta * (a ^ 4 / 24) < 0 := by
  dsimp only
  have h4 : 0 < C + 4 := by linarith
  have h5 : 0 < C + 5 := by linarith
  let a : ℝ := 8 * (C + 5)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hden : 0 < 48 * (C + 4) * (C + 5) := by
    positivity
  have hbase :
      48 * (C + 4) * (C + 5) < a ^ 2 := by
    dsimp [a]
    nlinarith [mul_pos h5 (by linarith : 0 < C + 8)]
  have hmul :
      a ^ 2 * (48 * (C + 4) * (C + 5)) < a ^ 4 := by
    have hsqa : 0 < a ^ 2 := sq_pos_of_pos ha
    have := mul_lt_mul_of_pos_left hbase hsqa
    nlinarith
  have hdiv :
      a ^ 2 < a ^ 4 / (48 * (C + 4) * (C + 5)) := by
    exact (lt_div_iff₀ hden).2 hmul
  have hetaform :
      coneEta C * (a ^ 4 / 24) =
        a ^ 4 / (48 * (C + 4) * (C + 5)) := by
    unfold coneEta
    field_simp [ne_of_gt h4, ne_of_gt h5]
    ring
  rw [hetaform]
  linarith

/-- Supplying the elementary analytic inequality
`a^4/24 <= cosh(a)-1` turns the quartic shadow into actual negativity of the
model at the explicit point. -/
theorem coneModel_negative_at_explicit_point
    (C : ℝ) (hC : 0 ≤ C)
    (hcosh :
      let a := 8 * (C + 5)
      a ^ 4 / 24 ≤ Real.cosh a - 1) :
    coneModel C (8 * (C + 5)) < 0 := by
  let a : ℝ := 8 * (C + 5)
  have heta : 0 ≤ coneEta C :=
    le_of_lt (coneEta_pos C hC)
  have hshadow := explicit_negative_quartic_shadow C hC
  dsimp only at hshadow
  dsimp only at hcosh
  have hweighted :
      coneEta C * (a ^ 4 / 24) ≤
        coneEta C * (Real.cosh a - 1) :=
    mul_le_mul_of_nonneg_left hcosh heta
  unfold coneModel
  change a ^ 2 - coneEta C * (Real.cosh a - 1) < 0
  nlinarith

#print axioms cone_beta_mean_lower_bound
#print axioms bounded_mean_forces_half_mass
#print axioms coneEta_pos
#print axioms cone_response_margin_identity
#print axioms half_margin_subtraction
#print axioms coneModel_even
#print axioms coneModel_zero
#print axioms explicit_negative_quartic_shadow
#print axioms coneModel_negative_at_explicit_point

end Round221RH
end Millennium
