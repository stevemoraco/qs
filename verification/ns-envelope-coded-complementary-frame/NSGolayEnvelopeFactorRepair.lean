import Mathlib

open scoped BigOperators

namespace NSGolayEnvelopeFactorRepair

/-- Multiplying every channel by one common envelope multiplies total squared
power by the envelope square. -/
theorem common_envelope_pair_power
    (d g0 g1 E : ℝ)
    (hg : g0 ^ 2 + g1 ^ 2 = E) :
    (d * g0) ^ 2 + (d * g1) ^ 2 = d ^ 2 * E := by
  rw [← hg]
  ring

/-- The common envelope factors out of the eight tensor-species power. -/
theorem common_envelope_tensor_power
    (d a0 a1 b0 b1 c0 c1 EA EB EC : ℝ)
    (ha : a0 ^ 2 + a1 ^ 2 = EA)
    (hb : b0 ^ 2 + b1 ^ 2 = EB)
    (hc : c0 ^ 2 + c1 ^ 2 = EC) :
    (d * (a0 * b0 * c0)) ^ 2 + (d * (a0 * b0 * c1)) ^ 2
      + (d * (a0 * b1 * c0)) ^ 2 + (d * (a0 * b1 * c1)) ^ 2
      + (d * (a1 * b0 * c0)) ^ 2 + (d * (a1 * b0 * c1)) ^ 2
      + (d * (a1 * b1 * c0)) ^ 2 + (d * (a1 * b1 * c1)) ^ 2
      = d ^ 2 * (EA * EB * EC) := by
  rw [← ha, ← hb, ← hc]
  ring

/-- A common scalar factor preserves an exact inactive-code cancellation. -/
theorem common_factor_preserves_inactive_cancellation
    (CD CG0 CG1 : ℝ)
    (hcode : CG0 + CG1 = 0) :
    CD * CG0 + CD * CG1 = 0 := by
  rw [← mul_add, hcode, mul_zero]

/-- At an active code coordinate, the common factor transmits the full macro
coefficient, scaled only by the complementary zero-lag energy. -/
theorem common_factor_preserves_active_correlation
    (CD CG0 CG1 E : ℝ)
    (hcode : CG0 + CG1 = E) :
    CD * CG0 + CD * CG1 = CD * E := by
  rw [← mul_add, hcode]

/-- Nonzero macro correlation survives when the complementary zero-lag energy
is nonzero. -/
theorem active_macro_correlation_survives
    (CD CG0 CG1 E : ℝ)
    (hCD : CD ≠ 0)
    (hE : E ≠ 0)
    (hcode : CG0 + CG1 = E) :
    CD * CG0 + CD * CG1 ≠ 0 := by
  rw [← mul_add, hcode]
  exact mul_ne_zero hCD hE

/-- A finite delta-like code selector transmits exactly one macro coefficient. -/
theorem finite_delta_selector
    {n : ℕ} (i0 : Fin n) (w code : Fin n → ℝ) (E : ℝ)
    (hcode : ∀ i, code i = if i = i0 then E else 0) :
    ∑ i, w i * code i = w i0 * E := by
  classical
  simp [hcode]

/-- With one common envelope of pointwise magnitude `d`, the fixed-eight
coherent cap becomes `8 d^2 E`; the envelope may carry the mode-count growth
forbidden to a flat complementary frame. -/
theorem common_envelope_gain_budget
    (M c E d y : ℝ)
    (hE : 0 < E)
    (hgain : c ^ 2 * M * E ≤ y ^ 2)
    (hcap : y ^ 2 ≤ 8 * d ^ 2 * E) :
    c ^ 2 * M ≤ 8 * d ^ 2 := by
  have hscaled : (c ^ 2 * M) * E ≤ (8 * d ^ 2) * E := by
    calc
      (c ^ 2 * M) * E = c ^ 2 * M * E := by ring
      _ ≤ y ^ 2 := hgain
      _ ≤ 8 * d ^ 2 * E := hcap
      _ = (8 * d ^ 2) * E := by ring
  exact le_of_mul_le_mul_right hscaled hE

/-- Any common-envelope repair retaining a fixed `c * sqrt M` gain must itself
have squared pointwise magnitude at least `c^2 M / 8`. -/
theorem required_envelope_peak_floor
    (M c E d y : ℝ)
    (hE : 0 < E)
    (hgain : c ^ 2 * M * E ≤ y ^ 2)
    (hcap : y ^ 2 ≤ 8 * d ^ 2 * E) :
    c ^ 2 * M / 8 ≤ d ^ 2 := by
  have hbudget := common_envelope_gain_budget M c E d y hE hgain hcap
  linarith

/-- An `m`-mode all-ones envelope has squared coherent peak exactly `m` times
its coefficient energy. -/
theorem all_ones_envelope_peak_gain (m : ℕ) :
    (∑ _j : Fin m, (1 : ℝ)) ^ 2
      = (m : ℝ) * ∑ _j : Fin m, (1 : ℝ) ^ 2 := by
  simp [pow_two]

/-- Every nonnegative target squared envelope magnitude has an exact real
scalar factor. -/
theorem scalar_envelope_factor_exists
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ d : ℝ, d ^ 2 = M := by
  refine ⟨Real.sqrt M, ?_⟩
  exact Real.sq_sqrt hM

/-- If the common envelope has squared magnitude `M`, the fixed-eight cap
scales as `8 M E`; the previous finite fixed-frame contradiction disappears. -/
theorem envelope_mode_scale_is_consistent
    (M E : ℝ) (hM : 0 ≤ M) :
    ∃ d : ℝ, d ^ 2 = M ∧ 8 * d ^ 2 * E = 8 * M * E := by
  obtain ⟨d, hd⟩ := scalar_envelope_factor_exists M hM
  refine ⟨d, hd, ?_⟩
  rw [hd]

#print axioms common_envelope_pair_power
#print axioms common_envelope_tensor_power
#print axioms common_factor_preserves_inactive_cancellation
#print axioms common_factor_preserves_active_correlation
#print axioms active_macro_correlation_survives
#print axioms finite_delta_selector
#print axioms common_envelope_gain_budget
#print axioms required_envelope_peak_floor
#print axioms all_ones_envelope_peak_gain
#print axioms scalar_envelope_factor_exists
#print axioms envelope_mode_scale_is_consistent

end NSGolayEnvelopeFactorRepair
