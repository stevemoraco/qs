import Mathlib

/-!
# Helical parent return: finite scalar coefficient core

This file formalizes only the scalar identities obtained after the explicit
coplanar helical-basis calculation in the accompanying note:

* the exact sum of the two helicity-channel return coefficients;
* its equal-radius reduction;
* the uniform lower bound on the acute-angle interval; and
* the final lower- and upper-budget assemblies used for near-equal shells.

It does not formalize complex helical vectors, the Euler/Navier--Stokes
bilinear operator, localized packets, normal forms, shadowing, or blow-up.
-/

namespace NSGolayHelicalReturn

noncomputable section

/-- The scalar `+` helical triple-product coefficient. The argument `sdelta`
stands for `sin delta`. -/
def channelPlus (c d Q sdelta : ℝ) : ℝ :=
  (Real.sqrt 2 * sdelta / 4) * (1 + (c + d) / Q)

/-- The scalar `-` helical triple-product coefficient. -/
def channelMinus (c d Q sdelta : ℝ) : ℝ :=
  (Real.sqrt 2 * sdelta / 4) * (1 - (c + d) / Q)

/-- Closed form for the two-helicity aggregate parent-return coefficient. -/
def helicalAggregate (c d Q sdelta : ℝ) : ℝ :=
  sdelta ^ 2 / 4 *
    (d * (1 + (c + d) ^ 2 / Q ^ 2) - 2 * (c + d))

/-- BANKER: summing the two signed-helicity channels gives the exact closed
form used by the parent-return calculation. -/
theorem helical_channel_sum
    (c d Q sdelta : ℝ) (hQ : Q ≠ 0) :
    (d - Q) * channelPlus c d Q sdelta ^ 2 +
        (d + Q) * channelMinus c d Q sdelta ^ 2 =
      helicalAggregate c d Q sdelta := by
  unfold channelPlus channelMinus helicalAggregate
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  field_simp [hQ]
  rw [hsqrt]
  ring

/-- BANKER: under the cosine-law and sine-square identities for two equal
radius parents, the aggregate reduces to a polynomial in `cos delta`. -/
theorem equal_radius_aggregate_formula
    (N Q sdelta x : ℝ) (hQ0 : Q ≠ 0)
    (hsin : sdelta ^ 2 = 1 - x ^ 2)
    (hcos : Q ^ 2 = 2 * N ^ 2 * (1 - x)) :
    helicalAggregate N N Q sdelta =
      N * (3 * x - 1) * (1 + x) / 4 := by
  unfold helicalAggregate
  field_simp [hQ0]
  rw [hsin, hcos]
  ring

/-- CRITIC: on the acute interval `cos delta >= 1/2`, the exact aggregate
retains a fixed positive fraction of the parent frequency. There is no
automatic factor proportional to the small angle. -/
theorem equal_radius_polynomial_has_parent_scale_floor
    (N x : ℝ) (hN : 0 < N) (hx : (1 : ℝ) / 2 ≤ x) :
    3 * N / 16 ≤ N * (3 * x - 1) * (1 + x) / 4 := by
  have hleft : 0 ≤ x - (1 : ℝ) / 2 := by linarith
  have hright : 0 ≤ 3 * x + (7 : ℝ) / 2 := by linarith
  have hprod : 0 ≤ (x - (1 : ℝ) / 2) *
      (3 * x + (7 : ℝ) / 2) := mul_nonneg hleft hright
  have hNprod : 0 ≤ N * ((x - (1 : ℝ) / 2) *
      (3 * x + (7 : ℝ) / 2)) :=
    mul_nonneg (le_of_lt hN) hprod
  nlinarith

/-- CLEANER: combining the exact equal-radius formula with the acute-angle
condition yields the explicit `3N/16` lower bound. -/
theorem equal_radius_aggregate_has_parent_scale_floor
    (N Q sdelta x : ℝ)
    (hN : 0 < N) (hQ0 : Q ≠ 0) (hx : (1 : ℝ) / 2 ≤ x)
    (hsin : sdelta ^ 2 = 1 - x ^ 2)
    (hcos : Q ^ 2 = 2 * N ^ 2 * (1 - x)) :
    3 * N / 16 ≤ helicalAggregate N N Q sdelta := by
  rw [equal_radius_aggregate_formula N Q sdelta x hQ0 hsin hcos]
  exact equal_radius_polynomial_has_parent_scale_floor N x hN hx

/-- The exact arithmetic assembly behind the near-equal-shell lower estimate:
`3d/10` of positive contribution minus at most `7d/32` of negative
contribution leaves `13d/160`. -/
theorem near_equal_shell_budget_floor
    (d positivePart negativePart total : ℝ)
    (hpositive : 3 * d / 10 ≤ positivePart)
    (hnegative : negativePart ≤ 7 * d / 32)
    (htotal : total = positivePart - negativePart) :
    13 * d / 160 ≤ total := by
  nlinarith

/-- The exact arithmetic assembly behind the complementary upper estimate:
`d/16 + 81d/64 = 85d/64`, and subtracting a nonnegative term only lowers
the total. -/
theorem near_equal_shell_budget_ceiling
    (d basePart squarePart negativePart total : ℝ)
    (hbase : basePart ≤ d / 16)
    (hsquare : squarePart ≤ 81 * d / 64)
    (hnegative : 0 ≤ negativePart)
    (htotal : total = basePart + squarePart - negativePart) :
    total ≤ 85 * d / 64 := by
  nlinarith

/-- CRITIC countermodel to a proposed angular gain: at `N=1` and
`cos delta=1/2`, the equal-radius aggregate polynomial is exactly `3/16`,
not of a smaller order forced by an extra unspecified angle factor. -/
theorem endpoint_parent_scale_is_nonzero :
    (1 : ℝ) * (3 * ((1 : ℝ) / 2) - 1) *
        (1 + (1 : ℝ) / 2) / 4 = 3 / 16 := by
  norm_num

#print axioms helical_channel_sum
#print axioms equal_radius_aggregate_formula
#print axioms equal_radius_polynomial_has_parent_scale_floor
#print axioms equal_radius_aggregate_has_parent_scale_floor
#print axioms near_equal_shell_budget_floor
#print axioms near_equal_shell_budget_ceiling
#print axioms endpoint_parent_scale_is_nonzero

end

end NSGolayHelicalReturn
