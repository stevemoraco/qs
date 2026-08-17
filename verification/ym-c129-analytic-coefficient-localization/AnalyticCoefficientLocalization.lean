import Mathlib

/-!
# Degree-uniform analytic coefficient localization

An infinite graded coefficient family is measured by a nonnegative `tsum`.
Degree truncation is contractive, a uniformly scaled tail is bounded by the
same coefficientwise multiplier, and fixed bounded handoffs preserve the tail
exponent. These are the order-theoretic core of using a weighted analytic
coefficient `l1` norm instead of raw degree-dependent coefficient-functional
norms.

The file does not formalize holomorphic Taylor coefficients, Kirk's covariant
localization, replica--BKAR, Yang--Mills theory, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.AnalyticCoefficientLocalization

open scoped BigOperators ENNReal

noncomputable section

variable {ι : Type*}

/-- Total mass retained through degree `D`. -/
def projectedMass
    (degree : ι → ℕ) (D : ℕ) (mass : ι → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' i, if degree i ≤ D then mass i else 0

/-- Total mass strictly above degree `D`. -/
def tailMass
    (degree : ι → ℕ) (D : ℕ) (mass : ι → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' i, if D < degree i then mass i else 0

/-- A degree projection is contractive in the coefficient `l1` mass. -/
theorem projectedMass_le_total
    (degree : ι → ℕ) (D : ℕ) (mass : ι → ℝ≥0∞) :
    projectedMass degree D mass ≤ ∑' i, mass i := by
  unfold projectedMass
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases h : degree i ≤ D
  · simp [h]
  · simp [h]

/-- The complementary degree tail is also contractive. -/
theorem tailMass_le_total
    (degree : ι → ℕ) (D : ℕ) (mass : ι → ℝ≥0∞) :
    tailMass degree D mass ≤ ∑' i, mass i := by
  unfold tailMass
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases h : D < degree i
  · simp [h]
  · simp [h]

/-- Scaled mass strictly above degree `D`. -/
def scaledTailMass
    (degree : ι → ℕ) (D : ℕ)
    (scale mass : ι → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' i, if D < degree i then scale i * mass i else 0

/-- A uniform coefficientwise tail multiplier controls the full infinite
scaled tail. -/
theorem scaledTailMass_le_uniform
    (degree : ι → ℕ) (D : ℕ)
    (scale mass : ι → ℝ≥0∞) (Q : ℝ≥0∞)
    (hscale : ∀ i, D < degree i → scale i ≤ Q) :
    scaledTailMass degree D scale mass ≤ ∑' i, Q * mass i := by
  unfold scaledTailMass
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases h : D < degree i
  · simp only [h, if_true]
    gcongr
    exact hscale i h
  · simp [h]

/-- If the total coefficient mass has already been bounded after multiplying
by `Q`, the scaled tail inherits that same bound. -/
theorem scaledTailMass_le_envelope
    (degree : ι → ℕ) (D : ℕ)
    (scale mass : ι → ℝ≥0∞) (Q envelope : ℝ≥0∞)
    (hscale : ∀ i, D < degree i → scale i ≤ Q)
    (htotal : (∑' i, Q * mass i) ≤ envelope) :
    scaledTailMass degree D scale mass ≤ envelope := by
  exact le_trans
    (scaledTailMass_le_uniform degree D scale mass Q hscale)
    htotal

/-- A fixed bounded output handoff changes only the prefactor of a previously
controlled analytic tail. -/
theorem fixed_handoff_preserves_tail_bound
    (input output K Q total : ℝ≥0∞)
    (houtput : output ≤ K * input)
    (hinput : input ≤ Q * total) :
    output ≤ (K * Q) * total := by
  calc
    output ≤ K * input := houtput
    _ ≤ K * (Q * total) := by gcongr
    _ = (K * Q) * total := by rw [mul_assoc]

/-- Six fixed bounded handoffs preserve one common tail exponent and multiply
only the finite prefactor. -/
theorem six_handoffs_preserve_tail_bound
    (r0 r1 r2 r3 r4 r5 r6 : ℝ≥0∞)
    (K1 K2 K3 K4 K5 K6 Q total : ℝ≥0∞)
    (h0 : r0 ≤ Q * total)
    (h1 : r1 ≤ K1 * r0)
    (h2 : r2 ≤ K2 * r1)
    (h3 : r3 ≤ K3 * r2)
    (h4 : r4 ≤ K4 * r3)
    (h5 : r5 ≤ K5 * r4)
    (h6 : r6 ≤ K6 * r5) :
    r6 ≤ (K6 * K5 * K4 * K3 * K2 * K1 * Q) * total := by
  calc
    r6 ≤ K6 * r5 := h6
    _ ≤ K6 * (K5 * r4) := by gcongr
    _ ≤ K6 * (K5 * (K4 * r3)) := by gcongr
    _ ≤ K6 * (K5 * (K4 * (K3 * r2))) := by gcongr
    _ ≤ K6 * (K5 * (K4 * (K3 * (K2 * r1)))) := by gcongr
    _ ≤ K6 * (K5 * (K4 * (K3 * (K2 * (K1 * r0))))) := by gcongr
    _ ≤ K6 * (K5 * (K4 * (K3 * (K2 * (K1 * (Q * total)))))) := by gcongr
    _ = (K6 * K5 * K4 * K3 * K2 * K1 * Q) * total := by
      ac_rfl

/-- Finite scalar composition of a degree-uniform localization row with the
C128 sublinear supplier-growth repair. -/
theorem degree_uniform_row_pays_macrostep_cutoff
    (a b Γ D : ℝ)
    (hΓ : Γ ≤ a * D + b)
    (hbudget : b + 5 < (1 - a) * D) :
    Γ + 2 < D - 3 := by
  linarith

#print axioms projectedMass_le_total
#print axioms tailMass_le_total
#print axioms scaledTailMass_le_uniform
#print axioms scaledTailMass_le_envelope
#print axioms fixed_handoff_preserves_tail_bound
#print axioms six_handoffs_preserve_tail_bound
#print axioms degree_uniform_row_pays_macrostep_cutoff

end Millennium.YangMills.AnalyticCoefficientLocalization
