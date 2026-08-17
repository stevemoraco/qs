import Mathlib

/-!
# Macrostep cutoff-growth firewall

Finite logical and scalar core for auditing a localization-degree choice in a
macrostep contraction argument.

Pointwise finiteness of a supplier constant at every cutoff degree, together
with an unbounded localization gain, does not imply that some degree beats the
supplier's degree-dependent logarithmic exponent. A cross-degree growth bound
is load-bearing.

This file does not formalize Kirk's activity spaces, covariant localization,
replica--BKAR, Yang--Mills theory, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.MacrostepCutoffGrowthFirewall

/-- The source-facing localization remainder gain `delta_D = D - 3`. -/
def localizationGain (D : ℕ) : ℕ := D - 3

/-- A hostile but pointwise finite supplier exponent. It corresponds to
`supplier(D) = 2^(2D)` before the logarithm. -/
def hostileSupplierExponent (D : ℕ) : ℕ := 2 * D

/-- A degree-independent supplier exponent, used as the good comparison. -/
def constantSupplierExponent (_D : ℕ) : ℕ := 0

/-- The localization gain is unbounded even in the hostile family. -/
theorem localizationGain_unbounded (M : ℕ) :
    ∃ D : ℕ, M ≤ localizationGain D := by
  refine ⟨M + 3, ?_⟩
  simp [localizationGain]

/-- No degree can make `D - 3` beat the hostile supplier exponent plus the
fixed two-unit reserve. -/
theorem no_cutoff_closes_hostile_family (D : ℕ) :
    ¬ hostileSupplierExponent D + 2 < localizationGain D := by
  simp only [hostileSupplierExponent, localizationGain]
  omega

/-- Pointwise finiteness of every supplier exponent and unbounded localization
gain do not produce one admissible cutoff degree. -/
theorem pointwise_finite_and_unbounded_gain_are_insufficient :
    (∀ D : ℕ, ∃ Γ : ℕ, hostileSupplierExponent D = Γ) ∧
      (∀ M : ℕ, ∃ D : ℕ, M ≤ localizationGain D) ∧
      ¬ ∃ D : ℕ, hostileSupplierExponent D + 2 < localizationGain D := by
  refine ⟨?_, localizationGain_unbounded, ?_⟩
  · intro D
    exact ⟨hostileSupplierExponent D, rfl⟩
  · intro h
    rcases h with ⟨D, hD⟩
    exact (no_cutoff_closes_hostile_family D) hD

/-- A degree-independent supplier exponent does admit a cutoff. -/
theorem constant_supplier_has_good_cutoff :
    ∃ D : ℕ, constantSupplierExponent D + 2 < localizationGain D := by
  refine ⟨6, ?_⟩
  norm_num [constantSupplierExponent, localizationGain]

/-- Integer version of the hostile short-row exponent identity. -/
def hostileGamma (D : ℤ) : ℤ := 2 * D

/-- Integer version of `delta_D`. -/
def localizationDelta (D : ℤ) : ℤ := D - 3

/-- In the hostile family the power of the macrostep length is `D + 3`, not a
negative number. -/
theorem hostile_short_exponent_identity (D : ℤ) :
    hostileGamma D - localizationDelta D = D + 3 := by
  simp [hostileGamma, localizationDelta]
  ring

/-- The hostile short-row exponent is strictly positive at every nonnegative
degree. -/
theorem hostile_short_exponent_positive (D : ℤ) (hD : 0 ≤ D) :
    0 < hostileGamma D - localizationDelta D := by
  rw [hostile_short_exponent_identity]
  omega

/-- The exact real cutoff condition can be rewritten without the shifted
localization notation. -/
theorem macrostep_cutoff_gap_iff (Γ D : ℝ) :
    Γ + 2 < D - 3 ↔ Γ + 5 < D := by
  constructor <;> intro h <;> linarith

/-- A sublinear supplier-exponent envelope pays the macrostep cutoff once the
explicit budget is positive. -/
theorem sublinear_supplier_growth_pays_cutoff
    (a b Γ D : ℝ)
    (hΓ : Γ ≤ a * D + b)
    (hbudget : b + 5 < (1 - a) * D) :
    Γ + 2 < D - 3 := by
  linarith

/-- If the supplier exponent has slope at least one with nonnegative offset,
then no nonnegative cutoff can create the required strict exponent gap. -/
theorem linear_or_faster_supplier_blocks_nonnegative_cutoff
    (a b D : ℝ)
    (ha : 1 ≤ a)
    (hb : 0 ≤ b)
    (hD : 0 ≤ D) :
    ¬ (a * D + b + 2 < D - 3) := by
  intro h
  nlinarith

#print axioms localizationGain_unbounded
#print axioms no_cutoff_closes_hostile_family
#print axioms pointwise_finite_and_unbounded_gain_are_insufficient
#print axioms constant_supplier_has_good_cutoff
#print axioms hostile_short_exponent_identity
#print axioms hostile_short_exponent_positive
#print axioms macrostep_cutoff_gap_iff
#print axioms sublinear_supplier_growth_pays_cutoff
#print axioms linear_or_faster_supplier_blocks_nonnegative_cutoff

end Millennium.YangMills.MacrostepCutoffGrowthFirewall
