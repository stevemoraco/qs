import Mathlib

/-!
# Hodge / Mostaed automorphic-audit finite core

This file protects only the exact finite arithmetic and logical countermodels in
`HODGE_MOSTAED_AUTOMORPHIC_PARAMETER_INTERIOR_AUDIT_2026-08-12.md`.

It does not formalize Shimura varieties, theta correspondence, Arthur
parameters, intersection cohomology, algebraic cycles, or the Hodge conjecture.
-/

namespace HodgeMostaedAutomorphicAudit

/-- The real dimension of `SO(2,26)/(SO(2) × SO(26))` from the standard
    orthogonal-group dimension formula. -/
theorem so_2_26_real_dimension :
    (28 * 27 / 2 : ℕ) -
      ((2 * 1 / 2 : ℕ) + (26 * 25 / 2 : ℕ)) = 52 := by
  norm_num

/-- A Hermitian manifold of complex dimension 26 has real dimension 52. -/
theorem type_iv_complex_dimension_check :
    (2 : ℕ) * 26 = 52 := by
  norm_num

/-- The manuscript's claimed complex dimension 13 is not the corrected
    type-IV complex dimension 26. -/
theorem thirteen_ne_twenty_six : (13 : ℕ) ≠ 26 := by
  norm_num

/-- A genuine tensor/external product of dimensions 3 and 25 has dimension 75. -/
theorem tensor_dimension_three_twentyfive :
    (3 : ℕ) * 25 = 75 := by
  norm_num

/-- Thus the tensor-product reading cannot be 28-dimensional. -/
theorem tensor_dimension_not_twenty_eight :
    (3 : ℕ) * 25 ≠ 28 := by
  norm_num

/-- The orthogonal direct-sum reading has the intended total dimension. -/
theorem direct_sum_dimension_three_twentyfive :
    (3 : ℕ) + 25 = 28 := by
  norm_num

abbrev ActiveBlock := Fin 3
abbrev TrivialComplement := Fin 25
abbrev StandardSpace := Sum ActiveBlock TrivialComplement

/-- An arbitrary action on the active 3-block, fixing the 25-block. -/
def activeBlockAction (f : ActiveBlock → ActiveBlock) :
    StandardSpace → StandardSpace
  | Sum.inl i => Sum.inl (f i)
  | Sum.inr j => Sum.inr j

/-- An arbitrary action on the 25-block, fixing the active 3-block. -/
def complementBlockAction (g : TrivialComplement → TrivialComplement) :
    StandardSpace → StandardSpace
  | Sum.inl i => Sum.inl i
  | Sum.inr j => Sum.inr (g j)

/-- Every complement action commutes with every active-block action. -/
theorem block_actions_commute
    (f : ActiveBlock → ActiveBlock)
    (g : TrivialComplement → TrivialComplement) :
    Function.comp (activeBlockAction f) (complementBlockAction g) =
      Function.comp (complementBlockAction g) (activeBlockAction f) := by
  funext x
  cases x <;> rfl

/-- A concrete nontrivial permutation of the 25-dimensional complement. -/
def complementSwap (j : TrivialComplement) : TrivialComplement :=
  if j = 0 then 1 else if j = 1 then 0 else j

/-- The complement swap is not the identity. -/
theorem complementSwap_ne_id : complementSwap ≠ id := by
  intro h
  have h0 := congrFun h (0 : TrivialComplement)
  simp [complementSwap] at h0

/-- The corresponding standard-space action is nontrivial. -/
theorem complementBlockSwap_ne_id :
    complementBlockAction complementSwap ≠ id := by
  intro h
  have h0 := congrFun h (Sum.inr (0 : TrivialComplement))
  simp [complementBlockAction, complementSwap] at h0

/-- A 3-block plus a pointwise-trivial 25-block has a nontrivial commuting
    complement action.  This is the finite set-level shadow of the
    positive-dimensional block centralizer. -/
theorem nontrivial_complement_centralizer :
    ∃ g : StandardSpace → StandardSpace,
      g ≠ id ∧
      ∀ f : ActiveBlock → ActiveBlock,
        Function.comp g (activeBlockAction f) =
          Function.comp (activeBlockAction f) g := by
  refine ⟨complementBlockAction complementSwap,
    complementBlockSwap_ne_id, ?_⟩
  intro f
  exact (block_actions_commute f complementSwap).symm

/-- Finite logical model of a zero compact-support degree-zero source mapping
    to a nonzero degree-zero target. -/
def degreeZeroFromCompactSupport (x : Empty) : PUnit := x.elim

/-- The nonzero unit target is not in the image of the empty source. -/
theorem unit_not_in_compact_support_image :
    PUnit.unit ∉ Set.range degreeZeroFromCompactSupport := by
  rintro ⟨x, _⟩
  exact x.elim

inductive AbstractCycle where
  | wholeCompactification

def meetsOpen (_ : AbstractCycle) : Prop := True

def abstractCycleClass (_ : AbstractCycle) : PUnit := PUnit.unit

/-- A cycle can meet the open part while its degree-zero class is not in the
    compact-support image.  This is only the quantifier shadow of the
    codimension-zero topological counterexample. -/
theorem meeting_cycle_need_not_be_interior :
    ∃ z : AbstractCycle,
      meetsOpen z ∧
      abstractCycleClass z ∉ Set.range degreeZeroFromCompactSupport := by
  exact ⟨AbstractCycle.wholeCompactification, trivial,
    unit_not_in_compact_support_image⟩

#print axioms so_2_26_real_dimension
#print axioms type_iv_complex_dimension_check
#print axioms thirteen_ne_twenty_six
#print axioms tensor_dimension_three_twentyfive
#print axioms tensor_dimension_not_twenty_eight
#print axioms direct_sum_dimension_three_twentyfive
#print axioms block_actions_commute
#print axioms complementSwap_ne_id
#print axioms complementBlockSwap_ne_id
#print axioms nontrivial_complement_centralizer
#print axioms unit_not_in_compact_support_image
#print axioms meeting_cycle_need_not_be_interior

end HodgeMostaedAutomorphicAudit
