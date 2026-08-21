import Mathlib

/-!
# P versus NP: low-weight encoding capacity core

Finite Lean companion to RH C331.

This file formalizes only the trust-clean finite encoding logic:

* an injective encoding of `2^m` semantic objects into a code space of size `B`
  forces `2^m <= B`;
* a Boolean labeling factors through an encoder exactly when it is constant on
  every encoder fiber;
* one encoder can support every Boolean labeling exactly when it is injective.

The analytic Hamming-ball estimate

`sum_{i<=t} binom(N,i) <= (e*N/t)^t`

and the C329 asymptotic comparison are deliberately left outside the kernel.
This file does **not** formalize CLY hashing/high-girth graphs, C320/C329 support
recovery, Fan--Li--Yang/C276, SAT hardness, NP, or `P != NP`.
-/

namespace Millennium.PNP.LowWeightEncodingCapacity

/-- Pure finite-cardinality consumer: an injective semantic encoder cannot have
more inputs than codewords. -/
theorem injective_card_le
    {X C : Type*} [Fintype X] [Fintype C]
    (E : X → C) (hE : Function.Injective E) :
    Fintype.card X ≤ Fintype.card C := by
  exact Fintype.card_le_of_injective E hE

/-- If `2^m` semantic instances inject into `B` codewords, then `2^m <= B`. -/
theorem binary_semantic_capacity
    (m B : ℕ) (E : Fin (2 ^ m) → Fin B)
    (hE : Function.Injective E) :
    2 ^ m ≤ B := by
  simpa using Fintype.card_le_of_injective E hE

/-- A Boolean labeling factors through an encoder iff it is constant on every
encoder fiber. -/
theorem factor_through_iff_fiber_constant
    {X C : Type*} [Fintype X] [Fintype C]
    (E : X → C) (f : X → Bool) :
    (∃ D : C → Bool, ∀ x : X, f x = D (E x)) ↔
      (∀ x y : X, E x = E y → f x = f y) := by
  classical
  constructor
  · rintro ⟨D, hD⟩ x y hxy
    rw [hD x, hD y, hxy]
  · intro hf
    let D : C → Bool := fun c =>
      if h : ∃ x : X, E x = c then f (Classical.choose h) else false
    refine ⟨D, ?_⟩
    intro x
    have hex : ∃ y : X, E y = E x := ⟨x, rfl⟩
    simp only [D, dif_pos hex]
    exact hf x (Classical.choose hex) (Classical.choose_spec hex).symm

/-- An injective encoder can support every Boolean labeling by extending the
labeling arbitrarily off its image. -/
theorem injective_implies_universal_factorization
    {X C : Type*} [Fintype X] [Fintype C]
    (E : X → C) (hE : Function.Injective E) :
    ∀ f : X → Bool, ∃ D : C → Bool, ∀ x : X, f x = D (E x) := by
  intro f
  rw [factor_through_iff_fiber_constant E f]
  intro x y hxy
  exact congrArg f (hE hxy)

/-- Conversely, if one fixed encoder can support every Boolean labeling, then
it must be injective.  A collision is separated by the singleton indicator of
one colliding semantic point. -/
theorem universal_factorization_implies_injective
    {X C : Type*} [Fintype X] [Fintype C]
    (E : X → C)
    (h : ∀ f : X → Bool, ∃ D : C → Bool, ∀ x : X, f x = D (E x)) :
    Function.Injective E := by
  classical
  intro x y hxy
  by_contra hne
  let f : X → Bool := fun z => decide (z = x)
  obtain ⟨D, hD⟩ := h f
  have hlabel : f x = f y := by
    rw [hD x, hD y, hxy]
  have hyx : y ≠ x := by
    intro hyx
    exact hne hyx.symm
  simpa [f, hyx] using hlabel

/-- Exact quantifier firewall: universal label service is equivalent to
injectivity of the encoder. -/
theorem universal_factorization_iff_injective
    {X C : Type*} [Fintype X] [Fintype C]
    (E : X → C) :
    (∀ f : X → Bool, ∃ D : C → Bool, ∀ x : X, f x = D (E x)) ↔
      Function.Injective E := by
  constructor
  · exact universal_factorization_implies_injective E
  · exact injective_implies_universal_factorization E

#print axioms injective_card_le
#print axioms binary_semantic_capacity
#print axioms factor_through_iff_fiber_constant
#print axioms injective_implies_universal_factorization
#print axioms universal_factorization_implies_injective
#print axioms universal_factorization_iff_injective

end Millennium.PNP.LowWeightEncodingCapacity
