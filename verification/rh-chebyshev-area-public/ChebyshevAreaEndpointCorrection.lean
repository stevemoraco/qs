import Millennium.RH.ChebyshevAreaPrimeFinite

/-!
# Endpoint correction for the finite-prime Johnston criterion

The published strict sign begins at `x > 2`, whereas the previously banked
closed-interval discrete criterion includes `x = 2`. This file proves the
resulting counterexample and supplies the punctured repair.

It does not formalize Johnston's analytic theorem or prove RH.
-/

namespace Millennium.RH.ChebyshevAreaEndpointCorrection

open Set
open ChebyshevAreaPrimeFinite

noncomputable section

/-- The prime prefix through two contains only the prime `2`. -/
theorem thetaNat_two : thetaNat 2 = Real.log 2 := by
  norm_num [thetaNat, primeWeight]

/-- Elementary logarithm bound used only for the automatic first interval. -/
theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

/-- The prime-prefix center lies to the left of the first closed interval. -/
theorem thetaNat_two_le_two : thetaNat 2 ≤ 2 := by
  rw [thetaNat_two]
  linarith [log_two_le_one]

/-- The integrated prime area vanishes at the excluded source endpoint. -/
theorem primeArea_two_endpoint : primeArea 2 2 = 0 := by
  norm_num [primeArea, primeWeight]

/-- Consequently the closed-interval minimum at `n=2` is zero, not positive. -/
theorem unitIntervalMinimum_two : unitIntervalMinimum 2 = 0 := by
  unfold unitIntervalMinimum
  rw [if_pos thetaNat_two_le_two]
  exact primeArea_two_endpoint

/-- The previously stated closed-interval criterion is false at its first index. -/
theorem not_discreteJohnstonCriterion : ¬ DiscreteJohnstonCriterion := by
  intro h
  have h2 := h 2 (by omega)
  rw [unitIntervalMinimum_two] at h2
  linarith

/-- Exact factorization of the first prime-prefix parabola. -/
theorem primeArea_two_factorization (x : ℝ) :
    primeArea 2 x =
      (x - 2) * ((x + 2) / 2 - Real.log 2) := by
  norm_num [primeArea, primeWeight]
  ring

/-- The punctured first interval is strictly positive unconditionally. -/
theorem primeArea_two_pos_of_gt {x : ℝ} (hx : 2 < x) :
    0 < primeArea 2 x := by
  rw [primeArea_two_factorization]
  have hleft : 0 < x - 2 := sub_pos.mpr hx
  have hright : 0 < (x + 2) / 2 - Real.log 2 := by
    linarith [log_two_le_one]
  exact mul_pos hleft hright

/-- Correct closed-interval minimum ledger: start at `n=3`. -/
def CorrectedDiscreteJohnstonCriterion : Prop :=
  ∀ n : ℕ, 3 ≤ n → 0 < unitIntervalMinimum n

/-- Equivalent punctured formulation matching the source condition `x>2`. -/
def PuncturedPrimeAreaCriterion : Prop :=
  (∀ x : ℝ, 2 < x → x ≤ 3 → 0 < primeArea 2 x) ∧
    ∀ n : ℕ, 3 ≤ n →
      ∀ x ∈ Icc (n : ℝ) (n + 1 : ℝ), 0 < primeArea n x

/-- The corrected scalar minimum ledger is exactly the punctured finite-prime
unit-interval criterion; the first interval is automatic. -/
theorem correctedDiscreteJohnstonCriterion_iff_punctured :
    CorrectedDiscreteJohnstonCriterion ↔ PuncturedPrimeAreaCriterion := by
  constructor
  · intro h
    constructor
    · intro x hx _hx3
      exact primeArea_two_pos_of_gt hx
    · intro n hn
      exact (positive_on_unitInterval_iff n).2 (h n hn)
  · intro h n hn
    exact (positive_on_unitInterval_iff n).1 (h.2 n hn)

/-- The false stronger criterion would imply the corrected one, but the reverse
must not be used because the stronger criterion contradicts the endpoint. -/
theorem discreteJohnstonCriterion_implies_corrected
    (h : DiscreteJohnstonCriterion) :
    CorrectedDiscreteJohnstonCriterion := by
  intro n hn
  exact h n (by omega)

#print axioms thetaNat_two
#print axioms log_two_le_one
#print axioms thetaNat_two_le_two
#print axioms primeArea_two_endpoint
#print axioms unitIntervalMinimum_two
#print axioms not_discreteJohnstonCriterion
#print axioms primeArea_two_factorization
#print axioms primeArea_two_pos_of_gt
#print axioms correctedDiscreteJohnstonCriterion_iff_punctured
#print axioms discreteJohnstonCriterion_implies_corrected

end

end Millennium.RH.ChebyshevAreaEndpointCorrection
