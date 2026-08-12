import Mathlib

/-!
# Navier--Stokes routing-rank nontermination firewall

This file formalizes only the finite/logical core of the source audit in
`NS_STRICT_DESCENDANT_NONTERMINATION_2026-08-12.md`.

It does not formalize packets, Navier--Stokes solutions, compactness, typed
ledgers, or the Clay problem.
-/

namespace NSStrictDescendantNontermination

/-- Abstract routing rank.  The countermodel stays forever at rank five. -/
def routingRank (_ : ℕ) : ℕ := 5

/-- `child` is the next strict descendant of `parent` in the abstract chain. -/
def IsStrictDescendant (child parent : ℕ) : Prop := child = parent + 1

/-- The genuinely terminal alternatives are false in the countermodel. -/
def FiniteBudgetCharged (_ : ℕ) : Prop := False

def ZeroOutputCollapse (_ : ℕ) : Prop := False

def EndpointExcluded (_ : ℕ) : Prop := False

def RankDrops (n : ℕ) : Prop := routingRank (n + 1) < routingRank n

/-- Every state has a strict descendant and the routing rank is unchanged. -/
theorem strict_descendant_step_repeats (n : ℕ) :
    IsStrictDescendant (n + 1) n ∧
      routingRank (n + 1) = routingRank n := by
  simp [IsStrictDescendant, routingRank]

/-- The source-style one-step disjunction can hold at every stage solely
    through the strict-descendant alternative. -/
theorem routing_disjunction_holds_forever :
    ∀ n : ℕ,
      FiniteBudgetCharged n ∨
      IsStrictDescendant (n + 1) n ∨
      ZeroOutputCollapse n ∨
      RankDrops n ∨
      EndpointExcluded n := by
  intro n
  exact Or.inr (Or.inl (by simp [IsStrictDescendant]))

/-- None of the genuinely terminal alternatives ever occurs. -/
theorem all_genuine_exits_fail :
    ∀ n : ℕ,
      ¬ FiniteBudgetCharged n ∧
      ¬ ZeroOutputCollapse n ∧
      ¬ RankDrops n ∧
      ¬ EndpointExcluded n := by
  intro n
  simp [FiniteBudgetCharged, ZeroOutputCollapse, RankDrops,
    EndpointExcluded, routingRank]

/-- There is an infinite strict-descendant chain whose rank never decreases. -/
theorem infinite_constant_rank_descendant_chain :
    ∃ packet : ℕ → ℕ,
      (∀ n : ℕ,
        IsStrictDescendant (packet (n + 1)) (packet n)) ∧
      (∀ n : ℕ,
        routingRank (packet (n + 1)) = routingRank (packet n)) := by
  refine ⟨fun n => n, ?_, ?_⟩
  · intro n
    simp [IsStrictDescendant]
  · intro n
    simp [routingRank]

/-- No index terminates the descendant chain. -/
theorem no_terminal_index :
    ¬ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → ¬ IsStrictDescendant (n + 1) n := by
  rintro ⟨N, hN⟩
  exact (hN N le_rfl) (by simp [IsStrictDescendant])

#print axioms strict_descendant_step_repeats
#print axioms routing_disjunction_holds_forever
#print axioms all_genuine_exits_fail
#print axioms infinite_constant_rank_descendant_chain
#print axioms no_terminal_index

end NSStrictDescendantNontermination
