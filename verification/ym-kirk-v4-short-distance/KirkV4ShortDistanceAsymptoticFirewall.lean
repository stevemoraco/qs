import Mathlib

namespace Millennium.YangMills

/-!
# Long-distance control does not determine short-distance normalization

Finite scalar countermodels only. No Schwinger functions, distributions,
operator products, Yang--Mills, or Clay theorem are formalized.
-/

/-- A toy correlation with a free contact value and a fixed exponential tail. -/
noncomputable def tailCorrelation (contact : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then contact else ((1 : ℝ) / 2) ^ n

/-- The contact parameter is completely invisible at every positive time. -/
theorem tailCorrelation_agree_at_positive_time
    (a b : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    tailCorrelation a n = tailCorrelation b n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  simp [tailCorrelation, hn0]

/-- The two models with contacts zero and one really differ at time zero. -/
theorem tailCorrelation_contacts_differ :
    tailCorrelation 0 0 ≠ tailCorrelation 1 0 := by
  norm_num [tailCorrelation]

/-- Exact finite no-free-lunch witness: identical exponentially decaying tails
do not determine the contact/short-distance value. -/
theorem same_exponential_tail_different_contact :
    ∃ c₀ c₁ : ℕ → ℝ,
      (∀ n : ℕ, 1 ≤ n →
        c₀ n = ((1 : ℝ) / 2) ^ n ∧
        c₁ n = ((1 : ℝ) / 2) ^ n) ∧
      c₀ 0 ≠ c₁ 0 := by
  refine ⟨tailCorrelation 0, tailCorrelation 1, ?_,
    tailCorrelation_contacts_differ⟩
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  constructor <;> simp [tailCorrelation, hn0]

/-- A coarse short-distance envelope after multiplication by the model scale. -/
def CoarseShortDistanceBound (c : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, |c n| ≤ (n : ℝ) + 1

/-- The normalized leading coefficient of a scale-linear model. -/
def HasNormalizedLeadingCoefficient (c : ℕ → ℝ) (A : ℝ) : Prop :=
  ∀ n : ℕ, c n / ((n : ℝ) + 1) = A

/-- Exact scale-linear model with prescribed normalized coefficient. -/
def scaledShortDistanceModel (A : ℝ) (n : ℕ) : ℝ :=
  A * ((n : ℝ) + 1)

/-- Every coefficient of absolute value at most one satisfies the same coarse
growth envelope. -/
theorem scaledShortDistanceModel_coarseBound
    (A : ℝ) (hA : |A| ≤ 1) :
    CoarseShortDistanceBound (scaledShortDistanceModel A) := by
  intro n
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  calc
    |scaledShortDistanceModel A n|
        = |A| * ((n : ℝ) + 1) := by
            simp [scaledShortDistanceModel, abs_mul, abs_of_nonneg hn]
    _ ≤ 1 * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hA hn
    _ = (n : ℝ) + 1 := by ring

/-- The scale-linear model has exactly its declared normalized coefficient. -/
theorem scaledShortDistanceModel_hasCoefficient
    (A : ℝ) :
    HasNormalizedLeadingCoefficient (scaledShortDistanceModel A) A := by
  intro n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp [scaledShortDistanceModel, hn]

/-- A common coarse seminorm/growth bound does not determine the normalized
short-distance coefficient. -/
theorem same_coarse_bound_different_leading_coefficients :
    ∃ c₀ c₁ : ℕ → ℝ,
      CoarseShortDistanceBound c₀ ∧
      CoarseShortDistanceBound c₁ ∧
      HasNormalizedLeadingCoefficient c₀ 0 ∧
      HasNormalizedLeadingCoefficient c₁ 1 ∧
      (0 : ℝ) ≠ 1 := by
  exact ⟨scaledShortDistanceModel 0, scaledShortDistanceModel 1,
    scaledShortDistanceModel_coarseBound 0 (by norm_num),
    scaledShortDistanceModel_coarseBound 1 (by norm_num),
    scaledShortDistanceModel_hasCoefficient 0,
    scaledShortDistanceModel_hasCoefficient 1,
    by norm_num⟩

#print axioms tailCorrelation_agree_at_positive_time
#print axioms tailCorrelation_contacts_differ
#print axioms same_exponential_tail_different_contact
#print axioms scaledShortDistanceModel_coarseBound
#print axioms scaledShortDistanceModel_hasCoefficient
#print axioms same_coarse_bound_different_leading_coefficients

end Millennium.YangMills
