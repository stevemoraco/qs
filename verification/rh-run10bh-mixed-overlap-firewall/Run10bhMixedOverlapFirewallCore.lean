import Mathlib

namespace Millennium.RH

/-- The Run10be unit split witness, restated locally for the Run10bh firewall. -/
noncomputable def run10bhWitness (A B : ℝ) : ℝ :=
  (A + 1) ^ 2 *
    ((101 / 100 : ℝ) - (A + B)) *
      (B + 1) ^ 2

/--
The part of the unit witness with at least one odd exponent in `A` or `B`.
The complementary terms are exactly the constant, the two quadratic squares,
and the mixed square `A^2 B^2`.
-/
noncomputable def run10bhOddRemainder (A B : ℝ) : ℝ :=
  -A ^ 3 * B ^ 2
  - 2 * A ^ 3 * B
  - A ^ 3
  - A ^ 2 * B ^ 3
  - (149 / 50 : ℝ) * A ^ 2 * B
  - 2 * A * B ^ 3
  - (149 / 50 : ℝ) * A * B ^ 2
  + (1 / 25 : ℝ) * A * B
  + (51 / 50 : ℝ) * A
  - B ^ 3
  + (51 / 50 : ℝ) * B

/--
Exact even/odd decomposition of the Run10be unit witness:

`W = 101/100 - (99/100)(A^2+B^2) - (299/100)A^2B^2 + O_odd`.

This is finite polynomial algebra only; averaging over the natural prime window is
not encoded here.
-/
theorem run10bh_witness_even_odd_decomposition (A B : ℝ) :
    run10bhWitness A B =
      (101 / 100 : ℝ)
      - (99 / 100 : ℝ) * (A ^ 2 + B ^ 2)
      - (299 / 100 : ℝ) * (A ^ 2 * B ^ 2)
      + run10bhOddRemainder A B := by
  unfold run10bhWitness run10bhOddRemainder
  ring

/--
At the exact marginal second-moment shell `Q=1` and zero odd discrepancy, the
unit witness becomes negative exactly when the mixed-square overlap exceeds
`2/299`.
-/
theorem run10bh_exact_mixed_overlap_threshold (C : ℝ) :
    (101 / 100 : ℝ)
        - (99 / 100 : ℝ)
        - (299 / 100 : ℝ) * C < 0 ↔
      (2 / 299 : ℝ) < C := by
  constructor <;> intro h <;> nlinarith

/--
Robust one-sided reserve budget.  If the quadratic mass is within `eps2` from
below, the mixed-square overlap beats its exact threshold `2/299` by `delta`,
and the averaged odd remainder is at most `epsOdd`, then the averaged witness
is strictly negative as soon as

`99 eps2 + 100 epsOdd < 299 delta`.

The theorem is scalar algebra.  Producing `Q`, `C`, and `O` from the physical
natural window remains the analytic/arithmetic source debt.
-/
theorem run10bh_overlap_plus_odd_budget
    (Q C O eps2 delta epsOdd : ℝ)
    (hQ : 1 - eps2 ≤ Q)
    (hC : (2 / 299 : ℝ) + delta ≤ C)
    (hO : O ≤ epsOdd)
    (hbudget : 99 * eps2 + 100 * epsOdd < 299 * delta) :
    (101 / 100 : ℝ)
        - (99 / 100 : ℝ) * Q
        - (299 / 100 : ℝ) * C
        + O < 0 := by
  nlinarith

/-- The four-point countermodel has total mass one. -/
theorem run10bh_countermodel_total_mass :
    (1 / 8 : ℝ) + (1 / 8 : ℝ) + (3 / 8 : ℝ) + (3 / 8 : ℝ) = 1 := by
  norm_num

/-- The four-point countermodel has centered `A`. -/
theorem run10bh_countermodel_A_mean :
    (1 / 8 : ℝ) * 1 + (1 / 8 : ℝ) * (-1) +
      (3 / 8 : ℝ) * 0 + (3 / 8 : ℝ) * 0 = 0 := by
  norm_num

/-- The four-point countermodel has centered `B`. -/
theorem run10bh_countermodel_B_mean :
    (1 / 8 : ℝ) * 0 + (1 / 8 : ℝ) * 0 +
      (3 / 8 : ℝ) * 1 + (3 / 8 : ℝ) * (-1) = 0 := by
  norm_num

/-- The four-point countermodel has exactly the Run10be marginal `A` variance. -/
theorem run10bh_countermodel_A_second :
    (1 / 8 : ℝ) * 1 ^ 2 + (1 / 8 : ℝ) * (-1) ^ 2 +
      (3 / 8 : ℝ) * 0 ^ 2 + (3 / 8 : ℝ) * 0 ^ 2 = (1 / 4 : ℝ) := by
  norm_num

/-- The four-point countermodel has exactly the Run10be marginal `B` variance. -/
theorem run10bh_countermodel_B_second :
    (1 / 8 : ℝ) * 0 ^ 2 + (1 / 8 : ℝ) * 0 ^ 2 +
      (3 / 8 : ℝ) * 1 ^ 2 + (3 / 8 : ℝ) * (-1) ^ 2 = (3 / 4 : ℝ) := by
  norm_num

/-- The four-point countermodel has vanishing marginal `A` cubic moment. -/
theorem run10bh_countermodel_A_third :
    (1 / 8 : ℝ) * 1 ^ 3 + (1 / 8 : ℝ) * (-1) ^ 3 +
      (3 / 8 : ℝ) * 0 ^ 3 + (3 / 8 : ℝ) * 0 ^ 3 = 0 := by
  norm_num

/-- The four-point countermodel has vanishing marginal `B` cubic moment. -/
theorem run10bh_countermodel_B_third :
    (1 / 8 : ℝ) * 0 ^ 3 + (1 / 8 : ℝ) * 0 ^ 3 +
      (3 / 8 : ℝ) * 1 ^ 3 + (3 / 8 : ℝ) * (-1) ^ 3 = 0 := by
  norm_num

/--
Despite the exact marginal shell, the countermodel has zero mixed-square
overlap because `A` and `B` live on disjoint atoms.
-/
theorem run10bh_countermodel_mixed_square_zero :
    (1 / 8 : ℝ) * (1 ^ 2 * 0 ^ 2) +
      (1 / 8 : ℝ) * ((-1) ^ 2 * 0 ^ 2) +
      (3 / 8 : ℝ) * (0 ^ 2 * 1 ^ 2) +
      (3 / 8 : ℝ) * (0 ^ 2 * (-1) ^ 2) = 0 := by
  norm_num

/-- The odd remainder also averages to zero in the sign-symmetric countermodel. -/
theorem run10bh_countermodel_odd_remainder_zero :
    (1 / 8 : ℝ) * run10bhOddRemainder 1 0 +
      (1 / 8 : ℝ) * run10bhOddRemainder (-1) 0 +
      (3 / 8 : ℝ) * run10bhOddRemainder 0 1 +
      (3 / 8 : ℝ) * run10bhOddRemainder 0 (-1) = 0 := by
  unfold run10bhOddRemainder
  norm_num

/--
Fatal marginal-only firewall: exact centering, exact marginal variances, and
zero marginal cubics do not force a negative Run10be witness mean.  The explicit
countermodel gives the positive value `1/50`.
-/
theorem run10bh_countermodel_witness_mean_positive :
    (1 / 8 : ℝ) * run10bhWitness 1 0 +
      (1 / 8 : ℝ) * run10bhWitness (-1) 0 +
      (3 / 8 : ℝ) * run10bhWitness 0 1 +
      (3 / 8 : ℝ) * run10bhWitness 0 (-1) = (1 / 50 : ℝ) := by
  unfold run10bhWitness
  norm_num

#check run10bh_witness_even_odd_decomposition
#print axioms run10bh_witness_even_odd_decomposition
#check run10bh_exact_mixed_overlap_threshold
#print axioms run10bh_exact_mixed_overlap_threshold
#check run10bh_overlap_plus_odd_budget
#print axioms run10bh_overlap_plus_odd_budget
#check run10bh_countermodel_total_mass
#print axioms run10bh_countermodel_total_mass
#check run10bh_countermodel_A_mean
#print axioms run10bh_countermodel_A_mean
#check run10bh_countermodel_B_mean
#print axioms run10bh_countermodel_B_mean
#check run10bh_countermodel_A_second
#print axioms run10bh_countermodel_A_second
#check run10bh_countermodel_B_second
#print axioms run10bh_countermodel_B_second
#check run10bh_countermodel_A_third
#print axioms run10bh_countermodel_A_third
#check run10bh_countermodel_B_third
#print axioms run10bh_countermodel_B_third
#check run10bh_countermodel_mixed_square_zero
#print axioms run10bh_countermodel_mixed_square_zero
#check run10bh_countermodel_odd_remainder_zero
#print axioms run10bh_countermodel_odd_remainder_zero
#check run10bh_countermodel_witness_mean_positive
#print axioms run10bh_countermodel_witness_mean_positive

end Millennium.RH
