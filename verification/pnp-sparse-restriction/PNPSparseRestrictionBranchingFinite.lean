import Mathlib

open scoped BigOperators

namespace MillenniumBraid

/-!
Finite cardinality cores for the sparse-restriction branching barrier and the
nonuniform counting separation.  These statements do not formalize Boolean
circuits, Chen--Li--Yang magnification, or a language in NP, and they do not
prove P versus NP.
-/

/-- If every output pattern occurs as the image of an element of a finite
support, then the number of patterns cannot exceed the support size. -/
theorem surjective_projection_card_le_support
    {X Y : Type*} [DecidableEq Y] [Fintype Y]
    (support : Finset X) (projection : X → Y)
    (hcover : ∀ y : Y, ∃ x ∈ support, projection x = y) :
    Fintype.card Y ≤ support.card := by
  have hsubset : Finset.univ ⊆ support.image projection := by
    intro y _hy
    obtain ⟨x, hx, hxy⟩ := hcover y
    exact Finset.mem_image.mpr ⟨x, hx, hxy⟩
  calc
    Fintype.card Y = Finset.univ.card := by simp
    _ ≤ (support.image projection).card := Finset.card_le_card hsubset
    _ ≤ support.card := Finset.card_image_le

/-- A positive support that realizes every Boolean pattern on `r` selected
coordinates must contain at least `2^r` strings. -/
theorem all_boolean_patterns_force_exponential_support
    {X : Type*} (r : ℕ)
    (support : Finset X) (projection : X → Fin r → Bool)
    (hcover : ∀ y : Fin r → Bool, ∃ x ∈ support, projection x = y) :
    2 ^ r ≤ support.card := by
  have hcard :=
    surjective_projection_card_le_support support projection hcover
  simpa using hcard

/-- Therefore a support of size at most `2^s` cannot realize all Boolean
patterns on any strictly larger set of coordinates. -/
theorem sparse_support_forbids_deeper_full_branching
    {X : Type*} (r s : ℕ)
    (support : Finset X) (projection : X → Fin r → Bool)
    (hsparse : support.card ≤ 2 ^ s)
    (hrs : s < r) :
    ¬ (∀ y : Fin r → Bool, ∃ x ∈ support, projection x = y) := by
  intro hcover
  have hlower : 2 ^ r ≤ support.card :=
    all_boolean_patterns_force_exponential_support r support projection hcover
  have hpow : 2 ^ s < 2 ^ r := by
    exact pow_lt_pow_right₀ (by norm_num : 1 < (2 : ℕ)) hrs
  omega

/-- Abstract pigeonhole core: if there are strictly more target truth tables
than candidate circuits, one target lies outside the circuit evaluation map. -/
theorem more_targets_than_circuits_gives_hard_target
    {Circuit Target : Type*} [Fintype Circuit] [Fintype Target]
    (evaluate : Circuit → Target)
    (hmore : Fintype.card Circuit < Fintype.card Target) :
    ∃ target : Target, ∀ circuit : Circuit, evaluate circuit ≠ target := by
  by_contra hnone
  push_neg at hnone
  have hsurj : Function.Surjective evaluate := by
    intro target
    exact hnone target
  have hcard : Fintype.card Target ≤ Fintype.card Circuit :=
    Fintype.card_le_of_surjective evaluate hsurj
  omega

/-- The same counting conclusion stated as non-surjectivity of the evaluator. -/
theorem target_count_exceeds_circuit_count_not_surjective
    {Circuit Target : Type*} [Fintype Circuit] [Fintype Target]
    (evaluate : Circuit → Target)
    (hmore : Fintype.card Circuit < Fintype.card Target) :
    ¬ Function.Surjective evaluate := by
  intro hsurj
  have hcard : Fintype.card Target ≤ Fintype.card Circuit :=
    Fintype.card_le_of_surjective evaluate hsurj
  omega

#print axioms MillenniumBraid.surjective_projection_card_le_support
#print axioms MillenniumBraid.all_boolean_patterns_force_exponential_support
#print axioms MillenniumBraid.sparse_support_forbids_deeper_full_branching
#print axioms MillenniumBraid.more_targets_than_circuits_gives_hard_target
#print axioms MillenniumBraid.target_count_exceeds_circuit_count_not_surjective

end MillenniumBraid
