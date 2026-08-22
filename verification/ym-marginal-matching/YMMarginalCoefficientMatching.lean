import Mathlib

/-!
# Yang--Mills marginal coefficient matching and norm-gauge firewall

Honesty status: this file formalizes only finite real-algebra identities and
inequalities used by the abstract RG audit.  It does not formalize running
couplings, infinite products, beta functions, transfer operators, Dobrushin
theory, Osterwalder--Schrader reconstruction, Yang--Mills theory, or the Clay
statement.
-/

namespace MillenniumBraid
namespace YMMarginalCoefficientMatching

theorem finiteMarginalCoefficientLedger
    (N : ℕ)
    (s h rX rY : ℕ → ℝ)
    (cX cY : ℝ) :
    (∑ i in Finset.range N,
      ((s i + cX * h i + rX i) - (s i + cY * h i + rY i))) =
      (cX - cY) * (∑ i in Finset.range N, h i) +
        ∑ i in Finset.range N, (rX i - rY i) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem matchedMarginalCoefficientLedger
    (N : ℕ)
    (s h rX rY : ℕ → ℝ)
    (c : ℝ) :
    (∑ i in Finset.range N,
      ((s i + c * h i + rX i) - (s i + c * h i + rY i))) =
        ∑ i in Finset.range N, (rX i - rY i) := by
  simpa using finiteMarginalCoefficientLedger N s h rX rY c c

theorem positiveMismatchDominatesResidual
    (m H H0 E residual : ℝ)
    (hm : 0 ≤ m)
    (hH : H0 ≤ H)
    (hresidual : -E ≤ residual) :
    m * H0 - E ≤ m * H + residual := by
  have hmul := mul_le_mul_of_nonneg_left hH hm
  linarith

theorem negativeMismatchDominatesResidual
    (m H H0 E residual : ℝ)
    (hm : m ≤ 0)
    (hH : H0 ≤ H)
    (hresidual : residual ≤ E) :
    m * H + residual ≤ m * H0 + E := by
  have hmul := mul_le_mul_of_nonpos_left hH hm
  linarith

theorem offDiagonalProductFixed
    (r : ℝ) (hr : 0 < r) :
    r * (1 / (4 * r)) = 1 / 4 := by
  field_simp [ne_of_gt hr]

theorem unweightedSecondRowBelowFirst
    (r : ℝ) (hr : 2 / 3 ≤ r) :
    1 / (4 * r) ≤ r := by
  have hr0 : 0 < r := by linarith
  have hfactor : 0 ≤ (r - 2 / 3) * (r + 2 / 3) := by
    exact mul_nonneg (by linarith) (by linarith)
  apply (div_le_iff₀ (by positivity : 0 < 4 * r)).2
  nlinarith

theorem fixedWeightedDobrushinRows
    (r : ℝ)
    (hr : 2 / 3 ≤ r)
    (hr1 : r < 1) :
    r / 2 ≤ 3 / 4 ∧ 1 / (2 * r) ≤ 3 / 4 := by
  constructor
  · linarith
  · have hr0 : 0 < r := by linarith
    apply (div_le_iff₀ (by positivity : 0 < 2 * r)).2
    nlinarith

theorem harmonicCertificateRecurrence
    (x : ℝ) (hx : 0 < x) :
    1 / (x + 1) = (1 - 1 / (x + 1)) * (1 / x) := by
  have hx1 : 0 < x + 1 := by linarith
  field_simp [ne_of_gt hx, ne_of_gt hx1]
  ring

theorem lowerCertificateBelowConstant
    (x : ℝ) (hx : 1 ≤ x) :
    0 < 1 / x ∧ 1 / x ≤ 1 := by
  have hx0 : 0 < x := by linarith
  constructor
  · exact one_div_pos.mpr hx0
  · exact (one_div_le_one₀ hx0).2 hx

theorem threePartMatchingBudget
    (scale coefficient residual epsilon : ℝ)
    (hscale : |scale| ≤ epsilon / 3)
    (hcoefficient : |coefficient| ≤ epsilon / 3)
    (hresidual : |residual| ≤ epsilon / 3) :
    |scale + coefficient + residual| ≤ epsilon := by
  calc
    |scale + coefficient + residual| ≤ |scale| + |coefficient| + |residual| := by
      calc
        |scale + coefficient + residual| = |(scale + coefficient) + residual| := by ring
        _ ≤ |scale + coefficient| + |residual| := abs_add _ _
        _ ≤ (|scale| + |coefficient|) + |residual| := by
          gcongr
          exact abs_add _ _
    _ ≤ epsilon := by linarith

#print axioms finiteMarginalCoefficientLedger
#print axioms matchedMarginalCoefficientLedger
#print axioms positiveMismatchDominatesResidual
#print axioms negativeMismatchDominatesResidual
#print axioms offDiagonalProductFixed
#print axioms unweightedSecondRowBelowFirst
#print axioms fixedWeightedDobrushinRows
#print axioms harmonicCertificateRecurrence
#print axioms lowerCertificateBelowConstant
#print axioms threePartMatchingBudget

end YMMarginalCoefficientMatching
end MillenniumBraid
