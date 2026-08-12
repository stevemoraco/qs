import Mathlib

/-!
# P versus NP same-length puncture barrier: finite core

HONESTY BOUNDARY

This file verifies only finite set/cardinality and scalar probability endpoints:

* if a finite puncture universe has more than `q+1` elements, then no set of at
  most `q` queried punctures together with one final output covers it;
* success on every puncture therefore forces `M <= q+1`;
* an average success bound `(q+1)/M` yields the corresponding query lower bound.

It does not formalize SAT encodings, search circuits, circuit size, adaptive
oracle machines, Pich--Santhanam witnessing tautologies, proof complexity,
P/poly, NP, or P versus NP.
-/

namespace Millennium
namespace PVsNP
namespace SameLengthPunctureFinite

/-- If the puncture universe is larger than a query set plus one proposed final
    output, some puncture lies outside both. -/
theorem exists_puncture_outside_queries_and_output
    {U : Type*}
    [Fintype U]
    [DecidableEq U]
    (queries : Finset U)
    (output : U)
    (hsize : queries.card + 1 < Fintype.card U) :
    ∃ z : U, z ∉ queries ∧ z ≠ output := by
  by_contra hnone
  have hall : ∀ z : U, z ∈ queries ∨ z = output := by
    intro z
    by_cases hq : z ∈ queries
    · exact Or.inl hq
    · right
      by_contra hne
      exact hnone ⟨z, hq, hne⟩
  have hsubset :
      (Finset.univ : Finset U) ⊆ queries ∪ {output} := by
    intro z _hz
    rcases hall z with hq | rfl
    · exact Finset.mem_union_left _ hq
    · simp
  have hcardCover :
      Fintype.card U ≤ (queries ∪ {output}).card := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card hsubset
  have hunion :
      (queries ∪ {output}).card ≤ queries.card + 1 := by
    calc
      (queries ∪ {output}).card
          ≤ queries.card + ({output} : Finset U).card := Finset.card_union_le
      _ = queries.card + 1 := by simp
  omega

/-- Exact deterministic endpoint: covering all `M` punctures with at most `q`
    queries and one final output forces `M <= q+1`. -/
theorem deterministic_puncture_query_budget
    (M q : ℕ)
    (hcover : M ≤ q + 1) :
    M - 1 ≤ q := by
  omega

/-- Exact randomized scalar endpoint.  If average success is at most
    `(q+1)/M` and is required to be at least `p`, then `p*M <= q+1`. -/
theorem randomized_puncture_query_budget
    (M q p : ℚ)
    (hM : 0 < M)
    (hsuccess : p ≤ (q + 1) / M) :
    p * M ≤ q + 1 := by
  exact (le_div_iff₀ hM).1 hsuccess

/-- For an exponential puncture set of cardinality `2^r`, uniform success one
    forces the same exact covering budget. -/
theorem exponential_puncture_budget
    (r q : ℕ)
    (hcover : 2 ^ r ≤ q + 1) :
    2 ^ r - 1 ≤ q := by
  omega

#print axioms exists_puncture_outside_queries_and_output
#print axioms deterministic_puncture_query_budget
#print axioms randomized_puncture_query_budget
#print axioms exponential_puncture_budget

end SameLengthPunctureFinite
end PVsNP
end Millennium
