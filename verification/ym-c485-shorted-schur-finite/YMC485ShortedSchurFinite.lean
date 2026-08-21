import Mathlib

/-!
# YM C485 finite shorted-Schur repair

Finite scalar and two-dimensional algebra only.  This file does not formalize
shorted operators on Hilbert space, transfer operators, constructive RG,
Osterwalder--Schrader reconstruction, continuum Yang--Mills, or a mass gap.
-/

namespace YM
namespace C485ShortedSchurFinite

/-- The positive two-coordinate Gram form used in the C483 hostile family. -/
def fullGramQ (rho x y : ℝ) : ℝ :=
  x ^ 2 + 2 * rho * x * y + y ^ 2

/-- The corrected observed part obtained by energy-form regression. -/
def shortedObservedQ (rho x y : ℝ) : ℝ :=
  (x + rho * y) ^ 2

/-- The corrected hidden Schur residual. -/
def shortedResidualQ (rho y : ℝ) : ℝ :=
  (1 - rho ^ 2) * y ^ 2

/-- A diagonal positive family with fixed observed coordinate and variable
hidden gap. -/
def diagonalGapQ (epsilon x y : ℝ) : ℝ :=
  x ^ 2 + epsilon * y ^ 2

/-- The corrected observed part plus hidden Schur residual reconstructs the
full Gram form exactly. -/
theorem shorted_exact_decomposition (rho x y : ℝ) :
    fullGramQ rho x y =
      shortedObservedQ rho x y + shortedResidualQ rho y := by
  unfold fullGramQ shortedObservedQ shortedResidualQ
  ring

/-- The corrected observed part is always nonnegative. -/
theorem shortedObservedQ_nonneg (rho x y : ℝ) :
    0 ≤ shortedObservedQ rho x y := by
  exact sq_nonneg (x + rho * y)

/-- If the original two-coordinate Gram matrix is positive (`rho^2 ≤ 1`),
then the hidden Schur residual is nonnegative. -/
theorem shortedResidualQ_nonneg
    {rho : ℝ} (hrho : rho ^ 2 ≤ 1) (y : ℝ) :
    0 ≤ shortedResidualQ rho y := by
  unfold shortedResidualQ
  exact mul_nonneg (sub_nonneg.mpr hrho) (sq_nonneg y)

/-- The hidden residual annihilates the selected first coordinate. -/
theorem shortedResidualQ_selected_zero (rho : ℝ) :
    shortedResidualQ rho 0 = 0 := by
  norm_num [shortedResidualQ]

/-- Scalar block-Schur completion without division.  The mixed term is absorbed
into the observed square and the hidden coefficient is the Schur residual. -/
theorem scalar_schur_identity (c k s x y : ℝ) :
    c * x ^ 2 + 2 * (c * k) * x * y + (s + c * k ^ 2) * y ^ 2 =
      c * (x + k * y) ^ 2 + s * y ^ 2 := by
  ring

/-- Nonnegative observed block plus nonnegative hidden Schur residual makes the
complete scalar block form nonnegative. -/
theorem scalar_schur_nonneg
    {c k s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s) (x y : ℝ) :
    0 ≤ c * x ^ 2 + 2 * (c * k) * x * y +
      (s + c * k ^ 2) * y ^ 2 := by
  rw [scalar_schur_identity]
  exact add_nonneg
    (mul_nonneg hc (sq_nonneg (x + k * y)))
    (mul_nonneg hs (sq_nonneg y))

/-- The exact C483 `rho=1/2` hostile matrix has a positive corrected residual. -/
theorem half_corrected_residual_nonneg (y : ℝ) :
    0 ≤ shortedResidualQ (1 / 2) y := by
  apply shortedResidualQ_nonneg
  norm_num

/-- The corrected decomposition repairs the literal C483 hostile vector. -/
theorem half_hostile_vector_repaired :
    fullGramQ (1 / 2) (-2) 1 =
      shortedObservedQ (1 / 2) (-2) 1 +
      shortedResidualQ (1 / 2) 1 := by
  exact shorted_exact_decomposition (1 / 2) (-2) 1

/-- The selected-coordinate Gram of the diagonal family is independent of the
hidden gap. -/
theorem diagonalGapQ_observed (epsilon x : ℝ) :
    diagonalGapQ epsilon x 0 = x ^ 2 := by
  simp [diagonalGapQ]

/-- The hidden unit vector sees exactly the hidden gap. -/
theorem diagonalGapQ_hidden (epsilon : ℝ) :
    diagonalGapQ epsilon 0 1 = epsilon := by
  simp [diagonalGapQ]

/-- Identical observed scalar data coexist with arbitrarily small positive
hidden Schur gaps.  This is the finite firewall against inferring a full gap
from the observed Gram alone. -/
theorem arbitrarily_small_hidden_gap
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧ epsilon < delta ∧
      (∀ x : ℝ, diagonalGapQ epsilon x 0 = x ^ 2) ∧
      diagonalGapQ epsilon 0 1 = epsilon := by
  refine ⟨delta / 2, by linarith, by linarith, ?_, ?_⟩
  · intro x
    exact diagonalGapQ_observed (delta / 2) x
  · exact diagonalGapQ_hidden (delta / 2)

#print axioms shorted_exact_decomposition
#print axioms shortedObservedQ_nonneg
#print axioms shortedResidualQ_nonneg
#print axioms shortedResidualQ_selected_zero
#print axioms scalar_schur_identity
#print axioms scalar_schur_nonneg
#print axioms half_corrected_residual_nonneg
#print axioms half_hostile_vector_repaired
#print axioms diagonalGapQ_observed
#print axioms diagonalGapQ_hidden
#print axioms arbitrarily_small_hidden_gap

end C485ShortedSchurFinite
end YM
