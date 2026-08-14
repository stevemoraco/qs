import Mathlib

/-!
# Type-I simultaneous moving-filter work-collapse firewall

Finite real analysis only.

The positive theorem says that a quantity with a quadratic small-scale bound
cannot sustain nonzero work against a uniformly bounded destination test.  This
is the scalar closure used after Giga--Miura Type-I rescaling: uniform local
`C^3` bounds make the differentiated resolved test uniformly bounded, while the
smooth commutator covariance is `O(σ²)`.

The negative theorem records the exact category boundary: without a uniform
test bound, an arbitrarily small raw factor can be paired with reciprocal
amplification and keep unit work.

These declarations do **not** formalize Navier--Stokes, mollification,
commutator stress, Giga--Miura, Runlong Yu's work pairing, or regularity.
-/

open Filter
open scoped Topology

namespace NSYuTypeISimultaneousWorkCollapse

/-- Multiplying a quadratic raw-factor bound by a uniform test bound preserves
the quadratic scale. -/
theorem abs_work_le_quadratic_scale
    {σ stress test C H : ℝ}
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hstress : |stress| ≤ C * σ ^ 2)
    (htest : |test| ≤ H) :
    |stress * test| ≤ C * H * σ ^ 2 := by
  rw [abs_mul]
  calc
    |stress| * |test| ≤ (C * σ ^ 2) * H := by
      exact mul_le_mul hstress htest (abs_nonneg test)
        (mul_nonneg hC (sq_nonneg σ))
    _ = C * H * σ ^ 2 := by ring

/-- A localized work bound with a fixed nonnegative volume factor. -/
theorem abs_localized_work_le_quadratic_scale
    {σ stress test volume C H : ℝ}
    (hvolume : 0 ≤ volume)
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hwork : |stress * test| ≤ C * H * σ ^ 2) :
    volume * |stress * test| ≤ volume * C * H * σ ^ 2 := by
  exact mul_le_mul_of_nonneg_left hwork hvolume

/-- Along any vanishing scale, quadratic raw factors paired with uniformly
bounded tests have work tending to zero. -/
theorem quadratic_stress_uniform_test_tendsto_zero
    (σ stress test : ℕ → ℝ) (C H : ℝ)
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hσ : Tendsto σ atTop (𝓝 0))
    (hstress : ∀ n, |stress n| ≤ C * (σ n) ^ 2)
    (htest : ∀ n, |test n| ≤ H) :
    Tendsto (fun n => stress n * test n) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => (σ n) ^ 2) atTop (𝓝 0) := by
    simpa [pow_two] using hσ.mul hσ
  have hquad :
      Tendsto (fun n => C * H * (σ n) ^ 2) atTop (𝓝 0) := by
    have hconst :
        Tendsto (fun _ : ℕ => C * H) atTop (𝓝 (C * H)) :=
      tendsto_const_nhds
    simpa using hconst.mul hsq
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hquad.neg hquad
  · intro n
    exact neg_le_of_abs_le
      (abs_work_le_quadratic_scale hC hH (hstress n) (htest n))
  · intro n
    exact le_of_abs_le
      (abs_work_le_quadratic_scale hC hH (hstress n) (htest n))

/-- Reciprocal amplification exactly cancels a nonzero quadratic raw factor. -/
theorem quadratic_raw_factor_reciprocal_test_unit_work
    {σ : ℝ} (hσ : σ ≠ 0) :
    σ ^ 2 * (σ ^ 2)⁻¹ = 1 := by
  exact mul_inv_cancel₀ (pow_ne_zero 2 hσ)

/-- An arbitrarily small positive scale can carry unit work if the destination
test is allowed reciprocal quadratic amplification. -/
theorem arbitrarily_small_scale_can_keep_unit_work
    (ε : ℝ) (hε : 0 < ε) :
    ∃ σ stress test : ℝ,
      0 < σ ∧ σ < ε ∧
      stress = σ ^ 2 ∧
      test = (σ ^ 2)⁻¹ ∧
      stress * test = 1 := by
  refine ⟨ε / 2, (ε / 2) ^ 2, ((ε / 2) ^ 2)⁻¹, ?_, ?_, rfl, rfl, ?_⟩
  · linarith
  · linarith
  · exact quadratic_raw_factor_reciprocal_test_unit_work (by linarith)

/-- A strict positive work floor is incompatible with a quadratic upper bound
once the scale itself is smaller than the explicit margin. -/
theorem quadratic_work_floor_forces_scale_floor
    {δ σ C H work : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hlow : δ ≤ |work|)
    (hup : |work| ≤ C * H * σ ^ 2) :
    δ ≤ C * H * σ ^ 2 := by
  exact hlow.trans hup

#print axioms abs_work_le_quadratic_scale
#print axioms abs_localized_work_le_quadratic_scale
#print axioms quadratic_stress_uniform_test_tendsto_zero
#print axioms quadratic_raw_factor_reciprocal_test_unit_work
#print axioms arbitrarily_small_scale_can_keep_unit_work
#print axioms quadratic_work_floor_forces_scale_floor

end NSYuTypeISimultaneousWorkCollapse
