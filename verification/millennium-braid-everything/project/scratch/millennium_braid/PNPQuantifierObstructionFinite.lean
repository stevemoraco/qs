import Mathlib

open scoped BigOperators

/-!
# P versus NP: finite range-compression and quantifier-budget cores

This file formalizes only finite combinatorial and scalar implications isolated
in the 2026-08-11 audit.  It does not formalize Boolean circuit semantics,
hardness magnification, complexity classes, or `P != NP`.
-/

namespace PNP
namespace QuantifierObstruction

/-- Keep the target label on a fixed pool and set every point outside the pool
false.  When the pool is small this is the finite core of a sparse language. -/
def sparsifyOn {X : Type*} [DecidableEq X]
    (pool : Finset X) (target : X → Bool) (x : X) : Bool :=
  if x ∈ pool then target x else false

/-- On the retained pool, sparsification does not change a target label. -/
theorem sparsifyOn_eq_of_mem {X : Type*} [DecidableEq X]
    (pool : Finset X) (target : X → Bool) (x : X)
    (hx : x ∈ pool) :
    sparsifyOn pool target x = target x := by
  simp [sparsifyOn, hx]

/-- The positive support of the sparsified target is contained in the pool. -/
def sparsePositiveSet {X : Type*} [DecidableEq X]
    (pool : Finset X) (target : X → Bool) : Finset X :=
  pool.filter (fun x => target x = true)

/-- Sparsification has at most as many positive points as the retained pool. -/
theorem sparsePositiveSet_card_le {X : Type*} [DecidableEq X]
    (pool : Finset X) (target : X → Bool) :
    (sparsePositiveSet pool target).card ≤ pool.card := by
  apply Finset.card_le_card
  intro x hx
  exact (Finset.mem_filter.mp hx).1

/-- Exact membership description of the positive support. -/
theorem sparsifyOn_eq_true_iff {X : Type*} [DecidableEq X]
    (pool : Finset X) (target : X → Bool) (x : X) :
    sparsifyOn pool target x = true ↔
      x ∈ sparsePositiveSet pool target := by
  simp [sparsifyOn, sparsePositiveSet]

/--
A circuit-dependent refuter whose entire output range is covered by one fixed
finite pool immediately gives a circuit-independent obstruction.  The target
may then be set to false outside that pool without losing the obstruction.
-/
theorem compressed_refuter_is_fixed_obstruction
    {Circuit X : Type*} [DecidableEq X]
    (eval : Circuit → X → Bool)
    (target : X → Bool)
    (refute : Circuit → X)
    (pool : Finset X)
    (hrange : ∀ circuit, refute circuit ∈ pool)
    (herr : ∀ circuit,
      eval circuit (refute circuit) ≠ target (refute circuit)) :
    ∀ circuit, ∃ x ∈ pool,
      eval circuit x ≠ sparsifyOn pool target x := by
  intro circuit
  refine ⟨refute circuit, hrange circuit, ?_⟩
  simpa [sparsifyOn, hrange circuit] using herr circuit

/-- A strict gap between a total witness budget and the maximum number of
satisfied witnesses forces at least one failed witness. -/
theorem strict_budget_forces_failure
    (total satisfied failed budget : ℕ)
    (hpartition : total = satisfied + failed)
    (hsupport : satisfied ≤ budget)
    (hstrict : budget < total) :
    0 < failed := by
  omega

/--
Finite averaging endpoint.  If the expected number of errors on a fixed pool is
at least one while every point has error probability at most `epsilon`, then
`card(pool) * epsilon` is at least one.
-/
theorem fixed_pool_pointwise_error_budget
    {X : Type*} [Fintype X]
    (errorProb : X → ℝ) (epsilon : ℝ)
    (hpointwise : ∀ x, errorProb x ≤ epsilon)
    (hone : 1 ≤ ∑ x, errorProb x) :
    1 ≤ (Fintype.card X : ℝ) * epsilon := by
  calc
    1 ≤ ∑ x, errorProb x := hone
    _ ≤ ∑ _x : X, epsilon := by
      apply Finset.sum_le_sum
      intro x _hx
      exact hpointwise x
    _ = (Fintype.card X : ℝ) * epsilon := by
      simp

/-- If `card(pool) * epsilon < 1`, the two averaging premises are incompatible. -/
theorem no_pointwise_error_below_inverse_pool
    {X : Type*} [Fintype X]
    (errorProb : X → ℝ) (epsilon : ℝ)
    (hpointwise : ∀ x, errorProb x ≤ epsilon)
    (hsmall : (Fintype.card X : ℝ) * epsilon < 1) :
    ¬ (1 ≤ ∑ x, errorProb x) := by
  intro hone
  have hbudget :=
    fixed_pool_pointwise_error_budget errorProb epsilon hpointwise hone
  linarith

/--
Exponent accounting for a tagged, componentwise polynomial-padding package.

* `verifyExp ≤ padExp * globalVerifyExp` is the class-preservation requirement;
* `padExp * globalCircuitExp ≤ hardExp` is the requirement that a circuit for
  the packaged language transfer below the component lower-bound exponent.

Both requirements force the cross-multiplied ratio budget below.
-/
theorem padding_tag_exponent_budget
    (verifyExp hardExp padExp globalCircuitExp globalVerifyExp : ℕ)
    (hverify : verifyExp ≤ padExp * globalVerifyExp)
    (htransfer : padExp * globalCircuitExp ≤ hardExp) :
    verifyExp * globalCircuitExp ≤ hardExp * globalVerifyExp := by
  calc
    verifyExp * globalCircuitExp
        ≤ (padExp * globalVerifyExp) * globalCircuitExp := by
          exact Nat.mul_le_mul hverify (le_refl globalCircuitExp)
    _ = (padExp * globalCircuitExp) * globalVerifyExp := by
          ac_rfl
    _ ≤ hardExp * globalVerifyExp := by
          exact Nat.mul_le_mul htransfer (le_refl globalVerifyExp)

/-- A violated cross-multiplied ratio budget rules out every padding exponent. -/
theorem no_padding_tag_when_ratio_budget_fails
    (verifyExp hardExp padExp globalCircuitExp globalVerifyExp : ℕ)
    (hbad : hardExp * globalVerifyExp <
      verifyExp * globalCircuitExp) :
    ¬ (verifyExp ≤ padExp * globalVerifyExp ∧
       padExp * globalCircuitExp ≤ hardExp) := by
  rintro ⟨hverify, htransfer⟩
  have hbudget := padding_tag_exponent_budget
    verifyExp hardExp padExp globalCircuitExp globalVerifyExp
    hverify htransfer
  exact (Nat.not_le_of_lt hbad) hbudget

/--
If every semantic pair needs two pair-specific tests, represented by disjoint
injective low- and high-test maps, then the test pool contains two copies of the
pair type.  This is the finite core of the quadratic test-pool warning for the
all-zero/all-one two-variable restriction template.
-/
theorem two_disjoint_injective_test_families_force_pool
    {Pair Test : Type*} [Fintype Pair] [Fintype Test]
    (low high : Pair → Test)
    (hlow : Function.Injective low)
    (hhigh : Function.Injective high)
    (hcross : ∀ p q, low p ≠ high q) :
    Fintype.card Pair + Fintype.card Pair ≤ Fintype.card Test := by
  let embed : Sum Pair Pair → Test := fun z =>
    match z with
    | Sum.inl p => low p
    | Sum.inr p => high p
  have hinj : Function.Injective embed := by
    intro a b hab
    cases a with
    | inl p =>
        cases b with
        | inl q =>
            have hpq : p = q := hlow (by simpa [embed] using hab)
            subst q
            rfl
        | inr q =>
            have heq : low p = high q := by simpa [embed] using hab
            exact False.elim ((hcross p q) heq)
    | inr p =>
        cases b with
        | inl q =>
            have heq : high p = low q := by simpa [embed] using hab
            exact False.elim ((hcross q p) heq.symm)
        | inr q =>
            have hpq : p = q := hhigh (by simpa [embed] using hab)
            subst q
            rfl
  have hcard : Fintype.card (Sum Pair Pair) ≤ Fintype.card Test :=
    Fintype.card_le_of_injective embed hinj
  simpa using hcard

#print axioms sparsifyOn_eq_of_mem
#print axioms sparsePositiveSet_card_le
#print axioms compressed_refuter_is_fixed_obstruction
#print axioms strict_budget_forces_failure
#print axioms fixed_pool_pointwise_error_budget
#print axioms no_pointwise_error_below_inverse_pool
#print axioms padding_tag_exponent_budget
#print axioms no_padding_tag_when_ratio_budget_fails
#print axioms two_disjoint_injective_test_families_force_pool

end QuantifierObstruction
end PNP
