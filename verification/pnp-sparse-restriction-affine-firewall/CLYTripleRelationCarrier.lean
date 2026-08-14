import Mathlib

namespace Millennium
namespace PNP
namespace CLYTripleRelationCarrier

def carrierByWeight (n w : ℕ) (mark : Prop) : Prop :=
  w = 1 ∨ w = n ∨ (w = 3 ∧ mark)

theorem low_boundary_not_three
    (w : ℕ) (hw : w ≤ 2) : w ≠ 3 := by
  omega

theorem high_boundary_not_three
    (n w : ℕ) (hn : 6 ≤ n) (hlo : n - 2 ≤ w) : w ≠ 3 := by
  omega

theorem carrier_agrees_on_cly_boundary
    (n w : ℕ) (mark : Prop)
    (hn : 6 ≤ n)
    (hboundary : w ≤ 2 ∨ (n - 2 ≤ w ∧ w ≤ n)) :
    carrierByWeight n w mark ↔ (w = 1 ∨ w = n) := by
  have hne : w ≠ 3 := by
    rcases hboundary with hlow | hhigh
    · exact low_boundary_not_three w hlow
    · exact high_boundary_not_three n w hn hhigh.1
  constructor
  · intro h
    rcases h with h1 | hn' | h3
    · exact Or.inl h1
    · exact Or.inr hn'
    · exact False.elim (hne h3.1)
  · intro h
    rcases h with h1 | hn'
    · exact Or.inl h1
    · exact Or.inr (Or.inl hn')

theorem low_pair_truth_table
    (n : ℕ) (hn : 6 ≤ n)
    (mark0 mark1a mark1b mark2 : Prop) :
    (¬ carrierByWeight n 0 mark0) ∧
      carrierByWeight n 1 mark1a ∧
      carrierByWeight n 1 mark1b ∧
      ¬ carrierByWeight n 2 mark2 := by
  constructor
  · intro h
    have hiff := carrier_agrees_on_cly_boundary n 0 mark0 hn (Or.inl (by omega))
    rcases hiff.mp h with h1 | heq <;> omega
  · constructor
    · exact Or.inl rfl
    · constructor
      · exact Or.inl rfl
      · intro h
        have hiff := carrier_agrees_on_cly_boundary n 2 mark2 hn (Or.inl (by omega))
        rcases hiff.mp h with h1 | heq <;> omega

theorem high_pair_truth_table
    (n : ℕ) (hn : 6 ≤ n)
    (mark00 mark01 mark10 mark11 : Prop) :
    (¬ carrierByWeight n (n - 2) mark00) ∧
      (¬ carrierByWeight n (n - 1) mark01) ∧
      (¬ carrierByWeight n (n - 1) mark10) ∧
      carrierByWeight n n mark11 := by
  constructor
  · intro h
    have hboundary : n - 2 ≤ n - 2 ∧ n - 2 ≤ n := by omega
    have hiff := carrier_agrees_on_cly_boundary n (n - 2) mark00 hn (Or.inr hboundary)
    have hbase := hiff.mp h
    rcases hbase with h1 | heq
    · omega
    · omega
  · constructor
    · intro h
      have hboundary : n - 2 ≤ n - 1 ∧ n - 1 ≤ n := by omega
      have hiff := carrier_agrees_on_cly_boundary n (n - 1) mark01 hn (Or.inr hboundary)
      have hbase := hiff.mp h
      rcases hbase with h1 | heq
      · omega
      · omega
    · constructor
      · intro h
        have hboundary : n - 2 ≤ n - 1 ∧ n - 1 ≤ n := by omega
        have hiff := carrier_agrees_on_cly_boundary n (n - 1) mark10 hn (Or.inr hboundary)
        have hbase := hiff.mp h
        rcases hbase with h1 | heq
        · omega
        · omega
      · exact Or.inr (Or.inl rfl)

theorem cubic_support_ledger (n : ℕ) :
    n + 1 + n.choose 3 = n + 1 + n.choose 3 := rfl

#print axioms low_boundary_not_three
#print axioms high_boundary_not_three
#print axioms carrier_agrees_on_cly_boundary
#print axioms low_pair_truth_table
#print axioms high_pair_truth_table
#print axioms cubic_support_ledger

end CLYTripleRelationCarrier
end PNP
end Millennium
