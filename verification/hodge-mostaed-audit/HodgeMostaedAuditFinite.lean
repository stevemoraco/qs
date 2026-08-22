import Mathlib

namespace HodgeMostaedAuditFinite

/-- In the regular-representation counterarchitecture, a degree-`2g` field can
    sit inside an ambient endomorphism algebra of dimension `2g^2`, which is
    strictly larger as soon as `g ≥ 2`. -/
theorem regular_representation_dimension_gap
    (g : ℕ) (hg : 2 ≤ g) :
    2 * g < 2 * g * g := by
  nlinarith

/-- The exact source-specific dimension gap: the distinguished CM field has
    rational dimension 12, while `M₆(F)` for an imaginary quadratic `F` has
    rational dimension 72. -/
theorem sixfold_dimension_gap :
    (12 : ℕ) < 72 := by
  norm_num

/-- A sufficient candidate-search criterion need not be exhaustive.  This is
    the logical quantifier firewall for the one-way Hecke criterion. -/
theorem sufficient_search_need_not_be_exhaustive :
    ∃ (point candidate : Prop),
      (candidate → point) ∧ ¬ (point → candidate) := by
  refine ⟨True, False, ?_, ?_⟩
  · intro h
    contradiction
  · intro h
    exact h trivial

/-- A failed search over candidates says nothing about points unless a converse
    implication has also been proved. -/
theorem no_point_of_noCandidate_requires_converse
    {Point Candidate : Prop}
    (hforward : Candidate → Point)
    (hnoCandidate : ¬ Candidate)
    (hconverse : Point → Candidate) :
    ¬ Point := by
  intro hPoint
  exact hnoCandidate (hconverse hPoint)

/-- Positive local dimension is incompatible with being an isolated
    zero-dimensional ambient deformation problem. -/
theorem positive_component_not_zero_dim
    {componentDim : ℕ}
    (h : 3 ≤ componentDim) :
    componentDim ≠ 0 := by
  omega

/-- The signature count used by the source-specific countermodel is exactly
    `3+3=6`. -/
theorem three_three_signature :
    3 + 3 = 6 := by
  norm_num

#print axioms regular_representation_dimension_gap
#print axioms sixfold_dimension_gap
#print axioms sufficient_search_need_not_be_exhaustive
#print axioms no_point_of_noCandidate_requires_converse
#print axioms positive_component_not_zero_dim
#print axioms three_three_signature

end HodgeMostaedAuditFinite
