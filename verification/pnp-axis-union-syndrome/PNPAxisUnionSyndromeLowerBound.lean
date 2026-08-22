import Mathlib

/-!
# Axis-union lower bound for linear side syndromes

This file formalizes a finite coding obstruction arising in the current
P-versus-NP short-cycle syndrome lane.

For an additive group `U`, consider the candidate family inside `U × U`
consisting of the two coordinate axes.  Every ambient vector is a difference
of two candidates.  Consequently, any additive syndrome that is injective on
that candidate family is already injective on the whole ambient product.

For `U = 𝔽₂^m`, the candidate family has `2^(m+1)-1` elements, while the
ambient space has `2^(2m)` elements.  Thus a linear syndrome separating this
explicit family needs a codomain of cardinality at least `2^(2m)`: the
factor-two `~2 log₂ M` bound is a genuine worst-case phenomenon, not merely a
loose union-bound artifact.

The file proves only finite additive-group and cardinal arithmetic.  It does
not formalize Boolean circuits, the Chen--Li--Yang construction, NP, P, or the
official P-versus-NP statement.
-/

namespace PNPAxisUnionSyndromeLowerBound

variable {U W : Type*} [AddCommGroup U] [AddCommGroup W]

def axes : Set (U × U) := {p | p.2 = 0 ∨ p.1 = 0}

@[simp] theorem left_mem_axes (x : U) : (x, 0) ∈ (axes : Set (U × U)) := by
  exact Or.inl rfl

@[simp] theorem right_mem_axes (y : U) : (0, y) ∈ (axes : Set (U × U)) := by
  exact Or.inr rfl

theorem every_vector_is_axis_difference (v : U × U) :
    ∃ a ∈ (axes : Set (U × U)), ∃ b ∈ (axes : Set (U × U)), v = a - b := by
  refine ⟨(v.1, 0), left_mem_axes v.1, (0, -v.2), right_mem_axes (-v.2), ?_⟩
  ext <;> simp

theorem every_nonzero_vector_is_distinct_axis_difference
    {v : U × U} (hv : v ≠ 0) :
    ∃ a ∈ (axes : Set (U × U)), ∃ b ∈ (axes : Set (U × U)),
      a ≠ b ∧ v = a - b := by
  obtain ⟨a, ha, b, hb, hab⟩ := every_vector_is_axis_difference v
  refine ⟨a, ha, b, hb, ?_, hab⟩
  intro hEq
  apply hv
  calc
    v = a - b := hab
    _ = 0 := by rw [hEq]; simp

theorem injective_of_injOn_axes
    (H : U × U →+ W)
    (hH : Set.InjOn H (axes : Set (U × U))) :
    Function.Injective H := by
  intro x y hxy
  let a : U × U := (x.1 - y.1, 0)
  let b : U × U := (0, -(x.2 - y.2))
  have ha : a ∈ (axes : Set (U × U)) := by
    exact Or.inl rfl
  have hb : b ∈ (axes : Set (U × U)) := by
    exact Or.inr rfl
  have hrep : x - y = a - b := by
    ext <;> simp [a, b]
  have hzero : H (a - b) = 0 := by
    rw [← hrep, map_sub, hxy, sub_self]
  have hmapSub : H a - H b = 0 := by
    simpa using hzero
  have hmap : H a = H b := sub_eq_zero.mp hmapSub
  have hab : a = b := hH ha hb hmap
  have hdiff : x - y = 0 := by
    rw [hrep, hab, sub_self]
  exact sub_eq_zero.mp hdiff

theorem card_square_le_of_injOn_axes
    [Fintype U] [Fintype W]
    (H : U × U →+ W)
    (hH : Set.InjOn H (axes : Set (U × U))) :
    Fintype.card U * Fintype.card U ≤ Fintype.card W := by
  have hcard := Fintype.card_le_of_injective H (injective_of_injOn_axes H hH)
  simpa using hcard

abbrev F2Vec (m : ℕ) := Fin m → ZMod 2

theorem card_f2vec (m : ℕ) : Fintype.card (F2Vec m) = 2 ^ m := by
  simp [F2Vec]

theorem f2_syndrome_card_lower
    (m r : ℕ)
    (H : F2Vec m × F2Vec m →+ F2Vec r)
    (hH : Set.InjOn H (axes : Set (F2Vec m × F2Vec m))) :
    (2 ^ m) * (2 ^ m) ≤ 2 ^ r := by
  have h := card_square_le_of_injOn_axes H hH
  simpa [F2Vec] using h

theorem same_nonzero_syndrome_refutes_injOn
    (H : U →+ W) (A : Set U) {c₁ c₂ : U}
    (hc₁A : c₁ ∈ A) (hc₂A : c₂ ∈ A)
    (hne : c₁ ≠ c₂) (hsame : H c₁ = H c₂) :
    ¬ Set.InjOn H A := by
  intro hInjective
  exact hne (hInjective hc₁A hc₂A hsame)

#print axioms every_vector_is_axis_difference
#print axioms every_nonzero_vector_is_distinct_axis_difference
#print axioms injective_of_injOn_axes
#print axioms card_square_le_of_injOn_axes
#print axioms card_f2vec
#print axioms f2_syndrome_card_lower
#print axioms same_nonzero_syndrome_refutes_injOn

end PNPAxisUnionSyndromeLowerBound
