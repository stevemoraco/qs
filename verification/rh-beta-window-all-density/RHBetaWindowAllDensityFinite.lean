import Mathlib

/-!
# RH beta-window all-density finite firewalls

HONESTY BOUNDARY

This file verifies only finite scalar and logical interfaces used in the
all-density exact-confluent beta-window theorem:

* a `2^{-m}` relative defect is at most one quarter for `m ≥ 2`;
* a quarter defect leaves a three-quarter diagonal margin;
* nonnegative lower-bound factors compose in the required direction;
* the rational constant `3/(8*12)` is exactly `1/32`;
* replacing a maximum observation time by a sum gives a weaker valid
  exponential floor;
* exact-confluent and perturbed-cluster inputs remain distinct.

It does not formalize Legendre/Chebyshev coefficient bounds, Laguerre tail
control, repeated integration by parts, Schur's test, the beta-window theorem,
Hardy spaces, zeta zeros, or RH.
-/

namespace MillenniumBraid
namespace RHBetaWindowAllDensityFinite

/-- Powers of one half beyond the second are at most one quarter. -/
theorem half_power_le_quarter
    (m : ℕ)
    (hm : 2 ≤ m) :
    (1 / 2 : ℝ) ^ m ≤ 1 / 4 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add]
  norm_num
  have hpow : (1 / 2 : ℝ) ^ n ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith [show 0 ≤ (1 / 2 : ℝ) ^ n by positivity]

/-- The abstract parameter calculation used after choosing `m=2K`. -/
theorem relative_defect_le_quarter
    (rho : ℝ)
    (m : ℕ)
    (hm : 2 ≤ m)
    (hrho : rho ≤ (1 / 2 : ℝ) ^ m) :
    rho ≤ 1 / 4 := by
  exact le_trans hrho (half_power_le_quarter m hm)

/-- A relative cross-term defect of at most one quarter leaves at least three
quarters of the diagonal energy. -/
theorem quarter_defect_leaves_three_quarters
    (diagonal cross : ℝ)
    (_hdiag : 0 ≤ diagonal)
    (hcross : |cross| ≤ (1 / 4 : ℝ) * diagonal) :
    (3 / 4 : ℝ) * diagonal ≤ diagonal + cross := by
  have hlower : -((1 / 4 : ℝ) * diagonal) ≤ cross :=
    neg_le_of_abs_le hcross
  nlinarith

/-- Composition of the exponential restriction, beta coercivity, and local
retention factors. -/
theorem compose_nonnegative_floors
    (Q I B D exponential beta localFloor : ℝ)
    (hexponential : 0 ≤ exponential)
    (hbeta : 0 ≤ beta)
    (hQ : exponential * I ≤ Q)
    (hI : beta * B ≤ I)
    (hB : localFloor * D ≤ B) :
    (exponential * beta * localFloor) * D ≤ Q := by
  calc
    (exponential * beta * localFloor) * D
        = exponential * (beta * (localFloor * D)) := by ring
    _ ≤ exponential * (beta * B) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hB hbeta) hexponential
    _ ≤ exponential * I := by
      exact mul_le_mul_of_nonneg_left hI hexponential
    _ ≤ Q := hQ

/-- Exact rational coefficient in the final displayed floor. -/
theorem final_rational_constant :
    (3 / 8 : ℝ) / 12 = 1 / 32 := by
  norm_num

/-- If an observation time is a maximum of two nonnegative times, replacing it
by their sum only decreases the resulting negative-exponential lower floor. -/
theorem exp_neg_max_ge_exp_neg_sum
    (x y : ℝ)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    Real.exp (-max x y) ≥ Real.exp (-(x + y)) := by
  apply Real.exp_le_exp.mpr
  have hmax : max x y ≤ x + y := by
    exact max_le (by linarith) (by linarith)
  linarith

/-- Every displayed beta-window floor is strictly positive once its algebraic
prefactors are positive. -/
theorem beta_floor_positive
    (time central denominator : ℝ)
    (hcentral : 0 < central)
    (hdenominator : 0 < denominator) :
    0 < Real.exp (-time) * central / denominator := by
  positivity

/-- Finite type firewall: exact polynomial-confluent blocks are not the same
input as clusters of distinct perturbed exponentials. -/
inductive ClusterInput where
  | exactConfluent
  | perturbedExponentials
  deriving DecidableEq

theorem exactConfluent_ne_perturbed :
    ClusterInput.exactConfluent ≠ ClusterInput.perturbedExponentials := by
  decide

/-- A theorem proved for the exact-confluent constructor remains there until a
separate synthesis comparison is supplied. -/
theorem exact_theorem_stays_exact
    (P : ClusterInput → Prop)
    (h : P ClusterInput.exactConfluent) :
    P ClusterInput.exactConfluent := h

#print axioms half_power_le_quarter
#print axioms relative_defect_le_quarter
#print axioms quarter_defect_leaves_three_quarters
#print axioms compose_nonnegative_floors
#print axioms final_rational_constant
#print axioms exp_neg_max_ge_exp_neg_sum
#print axioms beta_floor_positive
#print axioms exactConfluent_ne_perturbed
#print axioms exact_theorem_stays_exact

end RHBetaWindowAllDensityFinite
end MillenniumBraid
