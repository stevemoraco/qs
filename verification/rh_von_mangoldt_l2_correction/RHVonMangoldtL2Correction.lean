import Mathlib

namespace RHVonMangoldtL2Correction

/-- The elementary Hilbert-space correction estimate in scalar form. -/
theorem square_add_le_two_squares (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- A nonnegative weighted finite `L²` norm of a sum is controlled by twice
both component energies.  This is the finite algebra behind replacing the
prime-only dyadic error by its von Mangoldt completion. -/
theorem weighted_l2_add_le
    {ι : Type*}
    (s : Finset ι)
    (w f g : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i in s, w i * (f i + g i) ^ 2) ≤
      ∑ i in s, (2 * w i * f i ^ 2 + 2 * w i * g i ^ 2) := by
  apply Finset.sum_le_sum
  intro i hi
  calc
    w i * (f i + g i) ^ 2 ≤
        w i * (2 * f i ^ 2 + 2 * g i ^ 2) :=
      mul_le_mul_of_nonneg_left
        (square_add_le_two_squares (f i) (g i)) (hw i hi)
    _ = 2 * w i * f i ^ 2 + 2 * w i * g i ^ 2 := by ring

/-- Pointwise decomposition transfers directly to a finite weighted `L²`
correction bound. -/
theorem weighted_l2_perturbation
    {ι : Type*}
    (s : Finset ι)
    (w principal correction completed : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hdecomp : ∀ i ∈ s, completed i = principal i + correction i) :
    (∑ i in s, w i * completed i ^ 2) ≤
      ∑ i in s,
        (2 * w i * principal i ^ 2 + 2 * w i * correction i ^ 2) := by
  calc
    (∑ i in s, w i * completed i ^ 2) =
        ∑ i in s, w i * (principal i + correction i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hdecomp i hi]
    _ ≤ ∑ i in s,
        (2 * w i * principal i ^ 2 + 2 * w i * correction i ^ 2) :=
      weighted_l2_add_le s w principal correction hw

/-- If the principal energy and the completion error share one scale budget,
then the completed energy has the same scale budget up to an explicit
constant. -/
theorem common_scale_budget_transfer
    (completed principal correction principalConstant correctionConstant scale : ℝ)
    (hcompleted : completed ≤ 2 * principal + 2 * correction)
    (hprincipal : principal ≤ principalConstant * scale)
    (hcorrection : correction ≤ correctionConstant * scale) :
    completed ≤ 2 * (principalConstant + correctionConstant) * scale := by
  linarith

/-- Two energies differing by one common correction have equivalent existence
of a constant-times-scale bound. -/
theorem common_correction_budget_iff
    (first second correction correctionConstant scale : ℝ)
    (hfirst : first ≤ 2 * second + 2 * correction)
    (hsecond : second ≤ 2 * first + 2 * correction)
    (hcorrection : correction ≤ correctionConstant * scale) :
    (∃ C : ℝ, first ≤ C * scale) ↔
      ∃ C : ℝ, second ≤ C * scale := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨2 * (C + correctionConstant), ?_⟩
    exact common_scale_budget_transfer second first correction
      C correctionConstant scale hsecond hC hcorrection
  · rintro ⟨C, hC⟩
    refine ⟨2 * (C + correctionConstant), ?_⟩
    exact common_scale_budget_transfer first second correction
      C correctionConstant scale hfirst hC hcorrection

#print axioms square_add_le_two_squares
#print axioms weighted_l2_add_le
#print axioms weighted_l2_perturbation
#print axioms common_scale_budget_transfer
#print axioms common_correction_budget_iff

end RHVonMangoldtL2Correction
