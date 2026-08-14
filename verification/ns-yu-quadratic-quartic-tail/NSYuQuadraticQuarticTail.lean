import Mathlib

/-!
# Yu quadratic-work versus quartic-defect tail firewall

Finite weighted real algebra only. If a signed work coefficient has quadratic
amplitude growth, `|c i| ≤ C * q i ^ 2`, while the available defect currency is
quartic, then the total-variation tail above amplitude `R` is bounded by
`C / R^2` times the quartic currency. A bounded observable then loses at most
the same tail fraction times its bound.

This is the finite algebra suggested by Yu's full-profile covariance discussion:
covariance observables have quadratic growth while the defect budget is
quartic. It does **not** formalize the covariance/test-tensor landing, full
Young-profile representation, localization, recurrence, Navier--Stokes
regularity, or blow-up.
-/

open scoped BigOperators

noncomputable section

namespace NSYuQuadraticQuarticTail

variable {ι : Type*} [Fintype ι]

/-- Quartic increment currency. -/
def quarticCurrency (q : ι → ℝ) : ℝ :=
  ∑ i, (q i) ^ 4

/-- Total variation of a signed coefficient on the amplitude tail `q > R`. -/
def amplitudeTailTV (q c : ι → ℝ) (R : ℝ) : ℝ :=
  ∑ i, if R < q i then |c i| else 0

/-- Signed work retained below the amplitude threshold. -/
def retainedWork (q c k : ι → ℝ) (R : ℝ) : ℝ :=
  ∑ i, if R < q i then 0 else c i * k i

/-- Signed work discarded above the amplitude threshold. -/
def tailWork (q c k : ι → ℝ) (R : ℝ) : ℝ :=
  ∑ i, if R < q i then c i * k i else 0

/-- Exact split of signed work into retained and tail pieces. -/
theorem work_split (q c k : ι → ℝ) (R : ℝ) :
    (∑ i, c i * k i) = retainedWork q c k R + tailWork q c k R := by
  unfold retainedWork tailWork
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : R < q i <;> simp [hi]

omit [Fintype ι] in
/-- Pointwise quadratic growth plus `q > R ≥ 0` implies a quartic tail bound
whenever `C ≤ δ R²`. -/
theorem quadratic_pointwise_tail_le_quartic
    (q c : ι → ℝ) (R C δ : ℝ) (i : ι)
    (hR : 0 ≤ R)
    (hq : 0 ≤ q i)
    (hδ : 0 ≤ δ)
    (hCδ : C ≤ δ * R ^ 2)
    (hc : |c i| ≤ C * (q i) ^ 2)
    (hi : R < q i) :
    |c i| ≤ δ * (q i) ^ 4 := by
  have hprod : 0 ≤ (q i - R) * (q i + R) :=
    mul_nonneg (sub_nonneg.mpr hi.le) (add_nonneg hq hR)
  have hsq : R ^ 2 ≤ (q i) ^ 2 := by
    nlinarith
  calc
    |c i| ≤ C * (q i) ^ 2 := hc
    _ ≤ (δ * R ^ 2) * (q i) ^ 2 :=
      mul_le_mul_of_nonneg_right hCδ (sq_nonneg (q i))
    _ ≤ δ * (q i) ^ 4 := by
      have hmul := mul_le_mul_of_nonneg_left hsq
        (mul_nonneg hδ (sq_nonneg (q i)))
      nlinarith

/-- If `C ≤ δ R²`, the whole quadratic total-variation tail is at most `δ`
times the quartic currency. -/
theorem quadratic_tail_le_quartic_fraction
    (q c : ι → ℝ) (R C δ : ℝ)
    (hR : 0 ≤ R)
    (hq : ∀ i, 0 ≤ q i)
    (hδ : 0 ≤ δ)
    (hCδ : C ≤ δ * R ^ 2)
    (hc : ∀ i, |c i| ≤ C * (q i) ^ 2) :
    amplitudeTailTV q c R ≤ δ * quarticCurrency q := by
  unfold amplitudeTailTV quarticCurrency
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _hi
  by_cases hi : R < q i
  · simp only [hi, if_true]
    exact quadratic_pointwise_tail_le_quartic
      q c R C δ i hR (hq i) hδ hCδ (hc i) hi
  · simp only [hi, if_false]
    exact mul_nonneg hδ (pow_nonneg (hq i) 4)

/-- Explicit inverse-square tail form. -/
theorem quadratic_tail_le_quartic_div_sq
    (q c : ι → ℝ) (R C : ℝ)
    (hR : 0 < R)
    (hC : 0 ≤ C)
    (hq : ∀ i, 0 ≤ q i)
    (hc : ∀ i, |c i| ≤ C * (q i) ^ 2) :
    amplitudeTailTV q c R ≤
      (C / R ^ 2) * quarticCurrency q := by
  have hR0 : 0 ≤ R := hR.le
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hδ : 0 ≤ C / R ^ 2 := div_nonneg hC hR2.le
  have hCδ : C ≤ (C / R ^ 2) * R ^ 2 := by
    field_simp [ne_of_gt hR2]
  exact quadratic_tail_le_quartic_fraction
    q c R C (C / R ^ 2) hR0 hq hδ hCδ hc

/-- A bounded observable converts a total-variation tail bound into a signed
work-tail upper bound. -/
theorem tailWork_le_observable_bound
    (q c k : ι → ℝ) (R M : ℝ)
    (hk : ∀ i, |k i| ≤ M) :
    tailWork q c k R ≤ M * amplitudeTailTV q c R := by
  unfold tailWork amplitudeTailTV
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _hi
  by_cases hi : R < q i
  · simp only [hi, if_true]
    calc
      c i * k i ≤ |c i * k i| := le_abs_self _
      _ = |c i| * |k i| := abs_mul _ _
      _ ≤ |c i| * M :=
        mul_le_mul_of_nonneg_left (hk i) (abs_nonneg _)
      _ = M * |c i| := by ring
  · simp [hi]

/-- A positive quartic-normalized work floor survives a quadratic amplitude
tail. The exact remaining margin is `α - M δ`. -/
theorem quartic_margin_survives_quadratic_tail
    (q c k : ι → ℝ) (R C δ α M : ℝ)
    (hR : 0 ≤ R)
    (hq : ∀ i, 0 ≤ q i)
    (hδ : 0 ≤ δ)
    (hM : 0 ≤ M)
    (hCδ : C ≤ δ * R ^ 2)
    (hc : ∀ i, |c i| ≤ C * (q i) ^ 2)
    (hk : ∀ i, |k i| ≤ M)
    (hwork : α * quarticCurrency q ≤ ∑ i, c i * k i) :
    (α - M * δ) * quarticCurrency q ≤ retainedWork q c k R := by
  have htv := quadratic_tail_le_quartic_fraction
    q c R C δ hR hq hδ hCδ hc
  have htail := tailWork_le_observable_bound q c k R M hk
  have htailBudget :
      tailWork q c k R ≤ M * (δ * quarticCurrency q) :=
    htail.trans (mul_le_mul_of_nonneg_left htv hM)
  have hsplit := work_split q c k R
  calc
    (α - M * δ) * quarticCurrency q =
        α * quarticCurrency q - M * (δ * quarticCurrency q) := by ring
    _ ≤ (∑ i, c i * k i) - M * (δ * quarticCurrency q) :=
      sub_le_sub_right hwork _
    _ ≤ (∑ i, c i * k i) - tailWork q c k R := by
      linarith
    _ = retainedWork q c k R := by
      linarith

/-- Strict surviving margin and positive quartic currency force positive
retained work. -/
theorem positive_quartic_margin_gives_positive_retainedWork
    (q c k : ι → ℝ) (R C δ α M : ℝ)
    (hR : 0 ≤ R)
    (hq : ∀ i, 0 ≤ q i)
    (hδ : 0 ≤ δ)
    (hM : 0 ≤ M)
    (hCδ : C ≤ δ * R ^ 2)
    (hc : ∀ i, |c i| ≤ C * (q i) ^ 2)
    (hk : ∀ i, |k i| ≤ M)
    (hmargin : 0 < α - M * δ)
    (hcurrency : 0 < quarticCurrency q)
    (hwork : α * quarticCurrency q ≤ ∑ i, c i * k i) :
    0 < retainedWork q c k R := by
  have hfloor := quartic_margin_survives_quadratic_tail
    q c k R C δ α M hR hq hδ hM hCδ hc hk hwork
  have hpositive : 0 < (α - M * δ) * quarticCurrency q :=
    mul_pos hmargin hcurrency
  linarith

/-- The inverse-square decay exponent is sharp at the scalar level:
`R² * (C R²) = C R⁴`. -/
theorem inverse_square_tail_exponent_is_sharp (R C : ℝ) :
    R ^ 2 * (C * R ^ 2) = C * R ^ 4 := by
  ring

#print axioms quarticCurrency
#print axioms amplitudeTailTV
#print axioms retainedWork
#print axioms tailWork
#print axioms work_split
#print axioms quadratic_pointwise_tail_le_quartic
#print axioms quadratic_tail_le_quartic_fraction
#print axioms quadratic_tail_le_quartic_div_sq
#print axioms tailWork_le_observable_bound
#print axioms quartic_margin_survives_quadratic_tail
#print axioms positive_quartic_margin_gives_positive_retainedWork
#print axioms inverse_square_tail_exponent_is_sharp

end NSYuQuadraticQuarticTail
