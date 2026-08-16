import Mathlib

/-!
# Direct bounded-root contraction

Finite probability algebra only.

A normalized positive conditional expectation is contractive on bounded roots,
and a connected two-root covariance has one fixed bound.  These facts give a
direct scale-local repair for an intermediate retained-root estimate; they do
not infer that estimate from a later fully composed endpoint.

This file does not formalize conditional probability kernels, Kirk's Banach
spaces, replica--BKAR, a polymer expansion, Osterwalder--Schrader
reconstruction, Yang--Mills theory, or a mass gap.
-/

namespace YMBoundedConditionalRootContraction

/-- Finite normalized expectation with nonnegative weights. -/
def weightedMean {n : ℕ} (w f : Fin n → ℝ) : ℝ :=
  ∑ i, w i * f i

/-- Finite connected two-root expectation. -/
def weightedCovariance {n : ℕ} (w f g : Fin n → ℝ) : ℝ :=
  weightedMean w (fun i => f i * g i) -
    weightedMean w f * weightedMean w g

/-- A positive normalized finite expectation is an `L∞` contraction. -/
theorem weightedMean_abs_le
    {n : ℕ} (w f : Fin n → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1)
    (hf : ∀ i, |f i| ≤ B) :
    |weightedMean w f| ≤ B := by
  have hlow : -B ≤ weightedMean w f := by
    calc
      -B = ∑ i, w i * (-B) := by
        rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ i, w i * f i := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (abs_le.mp (hf i)).1 (hw i)
      _ = weightedMean w f := by rfl
  have hupp : weightedMean w f ≤ B := by
    calc
      weightedMean w f = ∑ i, w i * f i := by rfl
      _ ≤ ∑ i, w i * B := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (abs_le.mp (hf i)).2 (hw i)
      _ = B := by
        rw [← Finset.sum_mul, hsum, one_mul]
  apply abs_le.mpr
  constructor
  · linarith
  · linarith

/-- Product roots remain bounded under a positive normalized finite
expectation. -/
theorem weightedMean_product_abs_le
    {n : ℕ} (w f g : Fin n → ℝ) (Bf Bg : ℝ)
    (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1)
    (hf : ∀ i, |f i| ≤ Bf)
    (hg : ∀ i, |g i| ≤ Bg) :
    |weightedMean w (fun i => f i * g i)| ≤ Bf * Bg := by
  apply weightedMean_abs_le w (fun i => f i * g i) (Bf * Bg)
  · exact mul_nonneg hBf hBg
  · exact hw
  · exact hsum
  · intro i
    rw [abs_mul]
    exact mul_le_mul (hf i) (hg i) (abs_nonneg (g i)) hBf

/-- One connected two-root conditional has a fixed covariance bound. -/
theorem weightedCovariance_abs_le
    {n : ℕ} (w f g : Fin n → ℝ) (Bf Bg : ℝ)
    (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1)
    (hf : ∀ i, |f i| ≤ Bf)
    (hg : ∀ i, |g i| ≤ Bg) :
    |weightedCovariance w f g| ≤ 2 * (Bf * Bg) := by
  have hfg :
      |weightedMean w (fun i => f i * g i)| ≤ Bf * Bg :=
    weightedMean_product_abs_le w f g Bf Bg hBf hBg hw hsum hf hg
  have hfm : |weightedMean w f| ≤ Bf :=
    weightedMean_abs_le w f Bf hBf hw hsum hf
  have hgm : |weightedMean w g| ≤ Bg :=
    weightedMean_abs_le w g Bg hBg hw hsum hg
  have hprod :
      |weightedMean w f * weightedMean w g| ≤ Bf * Bg := by
    rw [abs_mul]
    exact mul_le_mul hfm hgm (abs_nonneg (weightedMean w g)) hBf
  have htri :
      |weightedMean w (fun i => f i * g i) -
          weightedMean w f * weightedMean w g| ≤
        |weightedMean w (fun i => f i * g i)| +
          |weightedMean w f * weightedMean w g| := by
    simpa only [Real.norm_eq_abs] using
      (norm_sub_le
        (weightedMean w (fun i => f i * g i))
        (weightedMean w f * weightedMean w g))
  calc
    |weightedCovariance w f g| =
        |weightedMean w (fun i => f i * g i) -
          weightedMean w f * weightedMean w g| := by rfl
    _ ≤ |weightedMean w (fun i => f i * g i)| +
          |weightedMean w f * weightedMean w g| := htri
    _ ≤ Bf * Bg + Bf * Bg := add_le_add hfg hprod
    _ = 2 * (Bf * Bg) := by ring

/-- Absolute nonexpansiveness is stable under composition. -/
theorem abs_nonexpansive_compose
    (T U : ℝ → ℝ)
    (hT : ∀ x, |T x| ≤ |x|)
    (hU : ∀ x, |U x| ≤ |x|)
    (x : ℝ) :
    |T (U x)| ≤ |x| := by
  exact (hT (U x)).trans (hU x)

/-- Once a connected two-root object has a fixed bound, every later normalized
conditional contraction preserves that same bound. -/
theorem transported_connected_root_bound
    (T : ℝ → ℝ) (c B : ℝ)
    (hT : ∀ x, |T x| ≤ |x|)
    (hc : |c| ≤ B) :
    |T c| ≤ B := by
  exact (hT c).trans hc

/-- The direct bounded-root theorem is genuinely different from endpoint
conditioning: a nonexpansive root transport cannot hide an amplified root. -/
theorem nonexpansive_transport_controls_root
    (T : ℝ → ℝ) (x B : ℝ)
    (hT : ∀ y, |T y| ≤ |y|)
    (hx : |x| ≤ B) :
    |T x| ≤ B := by
  exact (hT x).trans hx

#print axioms weightedMean_abs_le
#print axioms weightedMean_product_abs_le
#print axioms weightedCovariance_abs_le
#print axioms abs_nonexpansive_compose
#print axioms transported_connected_root_bound
#print axioms nonexpansive_transport_controls_root

end YMBoundedConditionalRootContraction
