import Mathlib

/-!
# Yang--Mills localization-degree quantifier firewall

This file formalizes the quantifier issue in an argument of the form

* for every cutoff degree `D`, a supplier constant is finite;
* an irrelevant-degree gain `delta D` tends to infinity;
* therefore choose `D` with `delta D > gamma D + 2`, where `gamma D`
  is the logarithmic size of that supplier constant.

The inference is false without uniform or relative-growth control on `gamma`.
The explicit countermodel is `delta D = D`, `gamma D = 2*D`.

This is finite arithmetic only. It does not formalize lattice gauge theory,
renormalization, Karcher blocking, the manuscript's actual constants, quantum
field theory, or the Yang--Mills Millennium theorem.
-/

namespace Millennium.YangMills.LocalizationDegreeQuantifierGap

/-- An irrelevant-degree gain that is unbounded. -/
def delta (D : ℕ) : ℕ := D

/-- A degree-dependent supplier exponent growing faster than the gain. -/
def gamma (D : ℕ) : ℕ := 2 * D

/-- Every degree has a perfectly finite supplier constant. -/
def supplier (D : ℕ) : ℕ := 2 ^ gamma D

/-- Pointwise finiteness is automatic in the countermodel. -/
theorem supplier_pointwise_finite (D : ℕ) :
    ∃ K : ℕ, K = supplier D := by
  exact ⟨supplier D, rfl⟩

/-- The irrelevant-degree gain tends to infinity in the cofinal/unbounded
sense needed by the printed degree-choice argument. -/
theorem delta_unbounded (M : ℕ) :
    ∃ D : ℕ, M < delta D := by
  exact ⟨M + 1, by simp [delta]⟩

/-- Nevertheless no degree beats its own degree-dependent supplier exponent. -/
theorem no_degree_beats_dependent_supplier :
    ¬ ∃ D : ℕ, gamma D + 2 < delta D := by
  rintro ⟨D, hD⟩
  simp [gamma, delta] at hD
  omega

/-- Exact countermodel: pointwise finite constants and an unbounded gain do not
imply the existence of a degree with positive exponent margin. -/
theorem pointwise_finiteness_and_unbounded_gain_insufficient :
    (∀ D : ℕ, ∃ K : ℕ, K = supplier D) ∧
    (∀ M : ℕ, ∃ D : ℕ, M < delta D) ∧
    ¬ ∃ D : ℕ, gamma D + 2 < delta D := by
  exact ⟨supplier_pointwise_finite, delta_unbounded,
    no_degree_beats_dependent_supplier⟩

/-- One sufficient repair: a degree-uniform bound on the supplier exponent,
together with an unbounded irrelevant-degree gain, makes the desired degree
choice valid. -/
theorem choose_degree_of_uniform_supplier_exponent
    (δ Γ : ℕ → ℕ) (G : ℕ)
    (hΓ : ∀ D, Γ D ≤ G)
    (hδ : ∀ M, ∃ D, M < δ D) :
    ∃ D, Γ D + 2 < δ D := by
  obtain ⟨D, hD⟩ := hδ (G + 2)
  refine ⟨D, ?_⟩
  have hΓD := hΓ D
  omega

/-- The exact weaker repair: it is enough to prove that the relative gap is
cofinal, not that the supplier exponent itself is uniformly bounded. -/
theorem choose_degree_of_relative_gap_cofinal
    (δ Γ : ℕ → ℕ)
    (hgap : ∀ M, ∃ D, M + Γ D < δ D) :
    ∃ D, Γ D + 2 < δ D := by
  obtain ⟨D, hD⟩ := hgap 2
  exact ⟨D, by omega⟩

/-- A nonpositive exponent margin cannot be used as a positive power-decay
margin. -/
theorem no_positive_margin_of_gain_le_supplier
    {gain supplierExponent : ℕ}
    (h : gain ≤ supplierExponent) :
    ¬ supplierExponent < gain := by
  exact not_lt_of_ge h

#print axioms supplier_pointwise_finite
#print axioms delta_unbounded
#print axioms no_degree_beats_dependent_supplier
#print axioms pointwise_finiteness_and_unbounded_gain_insufficient
#print axioms choose_degree_of_uniform_supplier_exponent
#print axioms choose_degree_of_relative_gap_cofinal
#print axioms no_positive_margin_of_gain_le_supplier

end Millennium.YangMills.LocalizationDegreeQuantifierGap
