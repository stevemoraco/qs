import Mathlib

namespace RHPrimorialLogEntropy

/-- The exact weighted Chebyshev deficit after expanding the prime staircase. -/
noncomputable def weightedDeficit (x theta q : ℝ) : ℝ :=
  x - 2 - theta * Real.log x + q

/-- The logarithmic Bregman tax separating the prime energy from the deficit. -/
noncomputable def gapTax (x theta : ℝ) : ℝ :=
  x - theta - theta * Real.log (x / theta)

/-- Prime-only endpoint energy
`theta + sum (log p)^2 - theta log theta - 2`. -/
noncomputable def primeEnergy (theta q : ℝ) : ℝ :=
  theta + q - theta * Real.log theta - 2

/-- The gap tax is a positive scale times `r - 1 - log r`. -/
theorem gapTax_eq_scaled
    {x theta : ℝ}
    (htheta : theta ≠ 0) :
    gapTax x theta =
      theta * (x / theta - 1 - Real.log (x / theta)) := by
  have hcancel : theta * (x / theta) = x := by
    field_simp [htheta]
  unfold gapTax
  rw [← hcancel]
  ring

/-- The logarithmic Bregman tax is nonnegative for positive endpoints. -/
theorem gapTax_nonneg
    {x theta : ℝ}
    (hx : 0 < x)
    (htheta : 0 < theta) :
    0 ≤ gapTax x theta := by
  have hratio : 0 < x / theta := div_pos hx htheta
  have hlog : Real.log (x / theta) ≤ x / theta - 1 :=
    Real.log_le_sub_one_of_pos hratio
  rw [gapTax_eq_scaled htheta.ne']
  exact mul_nonneg htheta.le (sub_nonneg.mpr hlog)

/-- Exact decomposition `weighted deficit = prime energy + Bregman tax`. -/
theorem weightedDeficit_eq_energy_add_gap
    {x theta q : ℝ}
    (hx : 0 < x)
    (htheta : 0 < theta) :
    weightedDeficit x theta q =
      primeEnergy theta q + gapTax x theta := by
  unfold weightedDeficit primeEnergy gapTax
  rw [Real.log_div hx.ne' htheta.ne']
  ring

/-- Positive prime energy forces a positive weighted deficit. -/
theorem primeEnergy_pos_implies_weightedDeficit_pos
    {x theta q : ℝ}
    (hx : 0 < x)
    (htheta : 0 < theta)
    (henergy : 0 < primeEnergy theta q) :
    0 < weightedDeficit x theta q := by
  rw [weightedDeficit_eq_energy_add_gap hx htheta]
  have hgap := gapTax_nonneg hx htheta
  linarith

/-- A negative weighted deficit forces negative prime energy. -/
theorem weightedDeficit_neg_implies_primeEnergy_neg
    {x theta q : ℝ}
    (hx : 0 < x)
    (htheta : 0 < theta)
    (hdeficit : weightedDeficit x theta q < 0) :
    primeEnergy theta q < 0 := by
  rw [weightedDeficit_eq_energy_add_gap hx htheta] at hdeficit
  have hgap := gapTax_nonneg hx htheta
  linarith

/-- The primorial endpoint inequality is exactly positivity of `primeEnergy`. -/
theorem primeEnergy_pos_iff
    (theta q : ℝ) :
    0 < primeEnergy theta q ↔
      theta * Real.log theta - theta + 2 < q := by
  unfold primeEnergy
  constructor <;> intro h <;> linarith

/-- Exact one-prime update of the endpoint energy. -/
theorem primeEnergy_increment
    (theta q ell : ℝ) :
    primeEnergy (theta + ell) (q + ell ^ 2) - primeEnergy theta q =
      ell + ell ^ 2 -
        ((theta + ell) * Real.log (theta + ell) - theta * Real.log theta) := by
  unfold primeEnergy
  ring

/-- Primitive whose endpoint difference is the exact prime-arrival increment. -/
noncomputable def arrivalPrimitive (ell u : ℝ) : ℝ :=
  ell * u - u * Real.log u + u

/-- Algebraic endpoint form of
`integral_theta^(theta+ell) log(exp ell / u) du`. -/
theorem primeEnergy_increment_eq_primitive_sub
    (theta q ell : ℝ) :
    primeEnergy (theta + ell) (q + ell ^ 2) - primeEnergy theta q =
      arrivalPrimitive ell (theta + ell) - arrivalPrimitive ell theta := by
  unfold primeEnergy arrivalPrimitive
  ring

/-- Any valid secant bound for `u log u` gives a nonnegative prime arrival. -/
theorem primeEnergy_increment_nonneg_of_secant_bound
    {theta q ell : ℝ}
    (hsecant :
      (theta + ell) * Real.log (theta + ell) - theta * Real.log theta
        ≤ ell + ell ^ 2) :
    0 ≤ primeEnergy (theta + ell) (q + ell ^ 2) - primeEnergy theta q := by
  rw [primeEnergy_increment]
  linarith

#print axioms gapTax_eq_scaled
#print axioms gapTax_nonneg
#print axioms weightedDeficit_eq_energy_add_gap
#print axioms primeEnergy_pos_implies_weightedDeficit_pos
#print axioms weightedDeficit_neg_implies_primeEnergy_neg
#print axioms primeEnergy_pos_iff
#print axioms primeEnergy_increment
#print axioms primeEnergy_increment_eq_primitive_sub
#print axioms primeEnergy_increment_nonneg_of_secant_bound

end RHPrimorialLogEntropy
