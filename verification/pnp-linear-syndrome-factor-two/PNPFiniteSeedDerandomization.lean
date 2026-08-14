import Mathlib

/-!
# Exact finite one-sided derandomization by double counting

For `N` deterministic seeds and `M` false inputs, suppose each false input is
accepted by at most `k` seeds.  If `M*k < N`, then one seed rejects every false
input.  If every seed has perfect completeness on all true inputs, that same
seed is an exact deterministic classifier.

The power-of-two corollary makes the union-bound currency explicit: if there
are `2^(s+t)` seeds, every false input is accepted by at most `2^s` seeds, and
there are fewer than `2^t` false inputs, then one exact seed exists.

No UNIT magnification theorem, circuit lower bound, `P`, `NP`, or Millennium
statement is formalized here.  Instantiating the theorem requires the exact
finite seed count, false-domain size, and pointwise error numerator from the
source problem.
-/

namespace PNPFiniteSeedDerandomization

/-- Matrix double counting. If every column has total weight at most `k` and
`M*k < N`, some row is identically zero. -/
theorem exists_zero_row_of_column_budget
    (N M k : ℕ)
    (bad : Fin N → Fin M → ℕ)
    (hcol : ∀ j, (∑ i, bad i j) ≤ k)
    (hbudget : M * k < N) :
    ∃ i, ∀ j, bad i j = 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hrow : ∀ i, 1 ≤ ∑ j, bad i j := by
    intro i
    obtain ⟨j, hj⟩ := hnone i
    have hone : 1 ≤ bad i j := Nat.one_le_iff_ne_zero.mpr hj
    have hterm : bad i j ≤ ∑ j', bad i j' := by
      exact Finset.single_le_sum
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    exact hone.trans hterm
  have hlower : N ≤ ∑ i, ∑ j, bad i j := by
    calc
      N = ∑ _i : Fin N, 1 := by simp
      _ ≤ ∑ i, ∑ j, bad i j := by
        apply Finset.sum_le_sum
        intro i hi
        exact hrow i
  have hswap : (∑ i, ∑ j, bad i j) = ∑ j, ∑ i, bad i j := by
    simpa using (Fintype.sum_comm bad)
  have hupper : (∑ j, ∑ i, bad i j) ≤ M * k := by
    calc
      (∑ j, ∑ i, bad i j) ≤ ∑ _j : Fin M, k := by
        apply Finset.sum_le_sum
        intro j hj
        exact hcol j
      _ = M * k := by simp [Nat.mul_comm]
  have hcontra : N ≤ M * k := by
    calc
      N ≤ ∑ i, ∑ j, bad i j := hlower
      _ = ∑ j, ∑ i, bad i j := hswap
      _ ≤ M * k := hupper
  exact (Nat.not_le_of_lt hbudget) hcontra

/-- Indicator specialization: if each false input is accepted by at most `k`
seeds and the total union-bound budget is strictly below the number of seeds,
one seed rejects every false input. -/
theorem exists_seed_rejects_all
    (N M k : ℕ)
    (accept : Fin N → Fin M → Prop)
    (hcol : ∀ j, (∑ i, if accept i j then 1 else 0) ≤ k)
    (hbudget : M * k < N) :
    ∃ i, ∀ j, ¬ accept i j := by
  classical
  obtain ⟨i, hi⟩ := exists_zero_row_of_column_budget
    N M k (fun i j => if accept i j then 1 else 0) hcol hbudget
  refine ⟨i, ?_⟩
  intro j haj
  have hz := hi j
  simp [haj] at hz

/-- Perfect completeness plus the strict finite union-bound budget gives one
exact deterministic classifier with no seed-dependent change of semantics. -/
theorem one_sided_exact_seed
    (N Y M k : ℕ)
    (accept : Fin N → Sum (Fin Y) (Fin M) → Prop)
    (hcomplete : ∀ i y, accept i (Sum.inl y))
    (hcol : ∀ j, (∑ i, if accept i (Sum.inr j) then 1 else 0) ≤ k)
    (hbudget : M * k < N) :
    ∃ i,
      (∀ y, accept i (Sum.inl y)) ∧
      (∀ j, ¬ accept i (Sum.inr j)) := by
  obtain ⟨i, hi⟩ := exists_seed_rejects_all
    N M k (fun i j => accept i (Sum.inr j)) hcol hbudget
  exact ⟨i, hcomplete i, hi⟩

/-- Elementary power-of-two budget used by the exact union-bound corollary. -/
theorem power_budget_lt
    (s t M : ℕ)
    (hM : M < (2 : ℕ) ^ t) :
    M * (2 : ℕ) ^ s < (2 : ℕ) ^ (s + t) := by
  have hpow : 0 < (2 : ℕ) ^ s := pow_pos (by norm_num) s
  have hmul := Nat.mul_lt_mul_of_pos_right hM hpow
  simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul

/-- Exact power-of-two derandomization.  A family with `2^(s+t)` seeds,
pointwise false-positive numerator at most `2^s`, and fewer than `2^t` false
inputs contains a seed with zero false positives. -/
theorem exists_exact_seed_of_power_budget
    (s t M : ℕ)
    (accept : Fin ((2 : ℕ) ^ (s + t)) → Fin M → Prop)
    (hcol : ∀ j,
      (∑ i, if accept i j then 1 else 0) ≤ (2 : ℕ) ^ s)
    (hM : M < (2 : ℕ) ^ t) :
    ∃ i, ∀ j, ¬ accept i j := by
  exact exists_seed_rejects_all
    ((2 : ℕ) ^ (s + t)) M ((2 : ℕ) ^ s)
    accept hcol (power_budget_lt s t M hM)

/-- One-sided power-of-two specialization with perfect completeness. -/
theorem one_sided_exact_seed_of_power_budget
    (s t Y M : ℕ)
    (accept : Fin ((2 : ℕ) ^ (s + t)) → Sum (Fin Y) (Fin M) → Prop)
    (hcomplete : ∀ i y, accept i (Sum.inl y))
    (hcol : ∀ j,
      (∑ i, if accept i (Sum.inr j) then 1 else 0) ≤ (2 : ℕ) ^ s)
    (hM : M < (2 : ℕ) ^ t) :
    ∃ i,
      (∀ y, accept i (Sum.inl y)) ∧
      (∀ j, ¬ accept i (Sum.inr j)) := by
  exact one_sided_exact_seed
    ((2 : ℕ) ^ (s + t)) Y M ((2 : ℕ) ^ s)
    accept hcomplete hcol (power_budget_lt s t M hM)

#print axioms exists_zero_row_of_column_budget
#print axioms exists_seed_rejects_all
#print axioms one_sided_exact_seed
#print axioms power_budget_lt
#print axioms exists_exact_seed_of_power_budget
#print axioms one_sided_exact_seed_of_power_budget

end PNPFiniteSeedDerandomization
