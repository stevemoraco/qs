import Mathlib

/-!
# Navier--Stokes magnitude-weighted direction firewall

Finite algebra companion to the Yu / Lei--Ren--Tian audit.

Lei--Ren--Tian's same-time angular obstruction at a singularity only guarantees
nonzero vorticity, not a uniform lower magnitude.  Yu's pairwise filtered
direction defect is magnitude weighted.  Thus a maximally separated same-time
pair can have arbitrarily small defect currency when both magnitudes are small.

The scalar model below uses the source-shaped asymmetric weight `a^2 * b * d`.
It does not formalize either paper's PDE theorem or any Navier--Stokes/Clay
conclusion.
-/

namespace NSMagnitudeWeightedDirectionFirewall

/-- Scalar shadow of Yu's magnitude-weighted pairwise direction currency:
`a,b` are nonnegative magnitudes and `d` is a direction-separation cost. -/
def weightedDirectionCost (a b d : ℝ) : ℝ := a ^ 2 * b * d

/-- Even unit directional separation costs only the cube of a common small
magnitude. -/
theorem equalSmallMagnitude_cost (eps : ℝ) :
    weightedDirectionCost eps eps 1 = eps ^ 3 := by
  unfold weightedDirectionCost
  ring

/-- Consequently a same-time separated pair with magnitude `eps` has cost at
most `eps` throughout the normalized range `0 <= eps <= 1`. -/
theorem equalSmallMagnitude_cost_le_eps
    {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1) :
    weightedDirectionCost eps eps 1 ≤ eps := by
  rw [equalSmallMagnitude_cost]
  nlinarith [sq_nonneg eps, mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- A common positive magnitude floor transfers monotonically into the weighted
pair currency when the direction-separation cost is nonnegative. -/
theorem magnitudeFloor_lower_bound
    {a b k d : ℝ}
    (hk : 0 ≤ k) (hd : 0 ≤ d)
    (ha : k ≤ a) (hb : k ≤ b) :
    weightedDirectionCost k k d ≤ weightedDirectionCost a b d := by
  have ha0 : 0 ≤ a := le_trans hk ha
  have hsq : k ^ 2 ≤ a ^ 2 := by nlinarith
  have hcubic : k ^ 2 * k ≤ a ^ 2 * b :=
    mul_le_mul hsq hb hk (sq_nonneg a)
  unfold weightedDirectionCost
  exact mul_le_mul_of_nonneg_right hcubic hd

/-- Positive magnitude thickness plus positive direction separation forces a
strictly positive source-shaped pair currency. -/
theorem positiveMagnitudeFloor_forces_positiveCost
    {a b k d : ℝ}
    (hk : 0 < k) (hd : 0 < d)
    (ha : k ≤ a) (hb : k ≤ b) :
    0 < weightedDirectionCost a b d := by
  have hlow : weightedDirectionCost k k d ≤ weightedDirectionCost a b d :=
    magnitudeFloor_lower_bound (le_of_lt hk) (le_of_lt hd) ha hb
  have hpos : 0 < weightedDirectionCost k k d := by
    unfold weightedDirectionCost
    positivity
  exact lt_of_lt_of_le hpos hlow

/-- The source-shaped cost at the common floor is exactly `k^3 d`, making the
missing quantitative currency explicit. -/
theorem commonFloor_cost_formula (k d : ℝ) :
    weightedDirectionCost k k d = k ^ 3 * d := by
  unfold weightedDirectionCost
  ring

#print axioms equalSmallMagnitude_cost
#print axioms equalSmallMagnitude_cost_le_eps
#print axioms magnitudeFloor_lower_bound
#print axioms positiveMagnitudeFloor_forces_positiveCost
#print axioms commonFloor_cost_formula

end NSMagnitudeWeightedDirectionFirewall
