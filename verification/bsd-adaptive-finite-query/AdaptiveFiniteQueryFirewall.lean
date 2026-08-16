import Mathlib

/-!
# BSD adaptive finite-query firewall

Finite arithmetic core of the BSD layer-tomography obstruction.
-/

namespace Millennium.BSD.AdaptiveFiniteQueryFirewall

/-- Exact layer-length model for a free `Z_p` module of rank `r`. -/
def freeLayer (r n : ℕ) : ℕ := r * n

/-- Exact layer-length model for rank `r` plus one cyclic torsion block of
exponent `p^E`.  The prime is irrelevant to the length formula. -/
def counterfeitLayer (r E n : ℕ) : ℕ := r * n + min n E

/-- Below the torsion exponent, one deep cyclic torsion block exactly imitates
one additional free direction. -/
theorem counterfeit_agrees_below_exponent
    (r E n : ℕ) (h : n ≤ E) :
    counterfeitLayer r E n = freeLayer (r + 1) n := by
  simp [counterfeitLayer, freeLayer, min_eq_left h, Nat.add_mul]

/-- Any finite depth ceiling `D` has a rank-minus-one counterfeit beyond it. -/
theorem arbitrary_depth_counterfeit
    (r D : ℕ) :
    ∃ E : ℕ, D < E ∧
      ∀ n : ℕ, n ≤ D →
        counterfeitLayer r E n = freeLayer (r + 1) n := by
  refine ⟨D + 1, by omega, ?_⟩
  intro n hn
  apply counterfeit_agrees_below_exponent
  omega

/-- Finite-query form: for any finite collection of queried depths bounded by
`D`, the same single counterfeit exponent `D+1` matches every answer. -/
theorem finite_query_counterfeit
    (r D : ℕ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, n ≤ D) :
    ∃ E : ℕ, D < E ∧
      ∀ n ∈ Q,
        counterfeitLayer r E n = freeLayer (r + 1) n := by
  refine ⟨D + 1, by omega, ?_⟩
  intro n hn
  apply counterfeit_agrees_below_exponent
  have hnD : n ≤ D := hQ n hn
  omega

/-- The transcript agreement is genuine rank ambiguity: the modeled free ranks
`r` and `r+1` are always distinct. -/
theorem finite_query_rank_ambiguity
    (r D : ℕ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, n ≤ D) :
    ∃ E : ℕ, D < E ∧ r ≠ r + 1 ∧
      ∀ n ∈ Q,
        counterfeitLayer r E n = freeLayer (r + 1) n := by
  refine ⟨D + 1, by omega, by omega, ?_⟩
  intro n hn
  apply counterfeit_agrees_below_exponent
  have hnD : n ≤ D := hQ n hn
  omega

#print axioms counterfeit_agrees_below_exponent
#print axioms arbitrary_depth_counterfeit
#print axioms finite_query_counterfeit
#print axioms finite_query_rank_ambiguity

end Millennium.BSD.AdaptiveFiniteQueryFirewall
