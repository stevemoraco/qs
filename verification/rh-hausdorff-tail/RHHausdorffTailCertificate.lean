import Mathlib

namespace MillenniumRun14

theorem rh_interval_sos_nonneg
    (x lo hi s0 s1 : ℝ)
    (hxlo : lo ≤ x)
    (hxhi : x ≤ hi)
    (hs0 : 0 ≤ s0)
    (hs1 : 0 ≤ s1) :
    0 ≤ s0 + (x - lo) * (hi - x) * s1 := by
  have hleft : 0 ≤ x - lo := sub_nonneg.mpr hxlo
  have hright : 0 ≤ hi - x := sub_nonneg.mpr hxhi
  have hprod : 0 ≤ (x - lo) * (hi - x) := mul_nonneg hleft hright
  have hweighted : 0 ≤ (x - lo) * (hi - x) * s1 :=
    mul_nonneg hprod hs1
  linarith

theorem rh_interval_sos_majorizes_one
    (x eps p s0 s1 : ℝ)
    (hx0 : 0 ≤ x)
    (hxe : x ≤ eps)
    (hs0 : 0 ≤ s0)
    (hs1 : 0 ≤ s1)
    (hrepr : p - 1 = s0 + x * (eps - x) * s1) :
    1 ≤ p := by
  have hnonneg := rh_interval_sos_nonneg x 0 eps s0 s1 hx0 hxe hs0 hs1
  norm_num at hnonneg
  linarith

theorem rh_interval_sos_nonnegative_on_unit
    (x p s0 s1 : ℝ)
    (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1)
    (hs0 : 0 ≤ s0)
    (hs1 : 0 ≤ s1)
    (hrepr : p = s0 + x * (1 - x) * s1) :
    0 ≤ p := by
  have hnonneg := rh_interval_sos_nonneg x 0 1 s0 s1 hx0 hx1 hs0 hs1
  norm_num at hnonneg
  linarith

theorem rh_finite_tail_majorant_sound
    {ι : Type*} [Fintype ι]
    (x w p : ι → ℝ)
    (eps : ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hmajor : ∀ i, x i ≤ eps → 1 ≤ p i)
    (hnonneg : ∀ i, 0 ≤ p i) :
    (∑ i, if x i ≤ eps then w i else 0) ≤
      ∑ i, w i * p i := by
  refine Finset.sum_le_sum ?_
  intro i hi
  by_cases htail : x i ≤ eps
  · simp [htail]
    have hmul := mul_le_mul_of_nonneg_left (hmajor i htail) (hw i)
    simpa using hmul
  · simp [htail]
    exact mul_nonneg (hw i) (hnonneg i)

theorem rh_finite_moment_objective_identity
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x w : ι → ℝ)
    (a : κ → ℝ)
    (deg : κ → ℕ) :
    (∑ i, w i * (∑ k, a k * x i ^ deg k)) =
      ∑ k, a k * (∑ i, w i * x i ^ deg k) := by
  calc
    (∑ i, w i * (∑ k, a k * x i ^ deg k))
        = ∑ i, ∑ k, w i * (a k * x i ^ deg k) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
    _ = ∑ k, ∑ i, w i * (a k * x i ^ deg k) := by
          rw [Finset.sum_comm]
    _ = ∑ k, a k * (∑ i, w i * x i ^ deg k) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring

theorem rh_finite_hausdorff_tail_certificate
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x w : ι → ℝ)
    (a : κ → ℝ)
    (deg : κ → ℕ)
    (eps : ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hmajor : ∀ i, x i ≤ eps →
      1 ≤ ∑ k, a k * x i ^ deg k)
    (hnonneg : ∀ i, 0 ≤ ∑ k, a k * x i ^ deg k) :
    (∑ i, if x i ≤ eps then w i else 0) ≤
      ∑ k, a k * (∑ i, w i * x i ^ deg k) := by
  calc
    (∑ i, if x i ≤ eps then w i else 0)
        ≤ ∑ i, w i * (∑ k, a k * x i ^ deg k) := by
            exact rh_finite_tail_majorant_sound
              x w (fun i => ∑ k, a k * x i ^ deg k) eps hw hmajor hnonneg
    _ = ∑ k, a k * (∑ i, w i * x i ^ deg k) := by
          exact rh_finite_moment_objective_identity x w a deg

#print axioms rh_interval_sos_nonneg
#print axioms rh_interval_sos_majorizes_one
#print axioms rh_interval_sos_nonnegative_on_unit
#print axioms rh_finite_tail_majorant_sound
#print axioms rh_finite_moment_objective_identity
#print axioms rh_finite_hausdorff_tail_certificate

end MillenniumRun14
