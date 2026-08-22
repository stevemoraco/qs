import Mathlib

/-!
# Round 214 P-versus-NP collision-oracle finite cores

This file formalizes finite hashing, union-budget, exact-recovery, and scalar
cost implications only. It does not formalize circuit syntax, sparse languages,
hardness magnification, promise classes, `P`, `NP`, or the official problem.
-/

namespace Millennium
namespace Round214PNP

open scoped BigOperators

/-- The collision oracle for a positive set `S`: some positive element hashes
onto the queried range value. -/
def CollisionOracle
    {U V R : Type*}
    (S : Finset U) (H : V → U → R) (v : V) (r : R) : Prop :=
  ∃ y ∈ S, H v y = r

/-- Every positive input is accepted when the oracle is queried at its own
hash value. -/
theorem positive_maps_into_collision_oracle
    {U V R : Type*}
    (S : Finset U) (H : V → U → R) (v : V) {x : U}
    (hx : x ∈ S) :
    CollisionOracle S H v (H v x) := by
  exact ⟨x, hx, rfl⟩

/-- Seeds on which two fixed inputs collide. -/
def pairBadSeeds
    {U V R : Type*} [Fintype V] [DecidableEq V] [DecidableEq R]
    (H : V → U → R) (x y : U) : Finset V :=
  Finset.univ.filter fun v => H v x = H v y

/-- Seeds on which `x` collides with at least one positive input. -/
def badSeeds
    {U V R : Type*} [Fintype V] [DecidableEq V] [DecidableEq R]
    (S : Finset U) (H : V → U → R) (x : U) : Finset V :=
  S.biUnion fun y => pairBadSeeds H x y

@[simp]
theorem mem_pairBadSeeds_iff
    {U V R : Type*} [Fintype V] [DecidableEq V] [DecidableEq R]
    (H : V → U → R) (x y : U) (v : V) :
    v ∈ pairBadSeeds H x y ↔ H v x = H v y := by
  simp [pairBadSeeds]

@[simp]
theorem mem_badSeeds_iff
    {U V R : Type*} [Fintype V] [DecidableEq V] [DecidableEq R]
    (S : Finset U) (H : V → U → R) (x : U) (v : V) :
    v ∈ badSeeds S H x ↔ ∃ y ∈ S, H v x = H v y := by
  simp [badSeeds, pairBadSeeds]

/-- Querying the collision oracle at `H_v(x)` is exactly membership of the seed
in the bad-seed set for `x`. -/
theorem collision_oracle_iff_mem_badSeeds
    {U V R : Type*} [Fintype V] [DecidableEq V] [DecidableEq R]
    (S : Finset U) (H : V → U → R) (x : U) (v : V) :
    CollisionOracle S H v (H v x) ↔ v ∈ badSeeds S H x := by
  simp [CollisionOracle, badSeeds, pairBadSeeds, eq_comm]

/-- Pairwise collision budgets union to the usual sparse-set false-positive
budget. No independence hypothesis is used. -/
theorem badSeeds_card_le_pair_budget
    {U V R : Type*} [Fintype V] [DecidableEq V] [DecidableEq R]
    (S : Finset U) (H : V → U → R) (x : U) (c : ℕ)
    (hpair : ∀ y ∈ S, (pairBadSeeds H x y).card ≤ c) :
    (badSeeds S H x).card ≤ S.card * c := by
  calc
    (badSeeds S H x).card
        ≤ ∑ y ∈ S, (pairBadSeeds H x y).card := by
          exact Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ S, c := by
          exact Finset.sum_le_sum fun y hy => hpair y hy
    _ = S.card * c := by
          simp [Nat.mul_comm]

/-- If the union-bound budget for all negative inputs is smaller than the seed
space, one seed avoids every negative bad set simultaneously. -/
theorem exists_seed_avoiding_bad_sets
    {U V : Type*} [Fintype V] [DecidableEq V]
    (Outside : Finset U) (Bad : U → Finset V) (b : ℕ)
    (hbad : ∀ x ∈ Outside, (Bad x).card ≤ b)
    (hbudget : Outside.card * b < Fintype.card V) :
    ∃ v : V, ∀ x ∈ Outside, v ∉ Bad x := by
  classical
  let allBad : Finset V := Outside.biUnion Bad
  have hcard : allBad.card ≤ Outside.card * b := by
    calc
      allBad.card ≤ ∑ x ∈ Outside, (Bad x).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ Outside, b := by
        exact Finset.sum_le_sum fun x hx => hbad x hx
      _ = Outside.card * b := by
        simp [Nat.mul_comm]
  have hproper : allBad ≠ (Finset.univ : Finset V) := by
    intro heq
    have hcardeq : allBad.card = Fintype.card V := by
      rw [heq]
      simp
    omega
  have hex : ∃ v : V, v ∉ allBad := by
    by_contra hn
    push_neg at hn
    apply hproper
    ext v
    simp [hn v]
  obtain ⟨v, hv⟩ := hex
  refine ⟨v, ?_⟩
  intro x hx hvx
  apply hv
  exact Finset.mem_biUnion.mpr ⟨x, hx, hvx⟩

/-- Under a pairwise collision budget strong enough to cover the whole finite
universe, one fixed seed makes the collision oracle recover `S` exactly. -/
theorem exists_exact_collision_seed_of_pair_budget
    {U V R : Type*}
    [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] [DecidableEq R]
    (S : Finset U) (H : V → U → R) (c : ℕ)
    (hpair : ∀ x ∉ S, ∀ y ∈ S,
      (pairBadSeeds H x y).card ≤ c)
    (hbudget :
      ((Finset.univ : Finset U) \ S).card * (S.card * c) <
        Fintype.card V) :
    ∃ v : V, ∀ x : U,
      (x ∈ S ↔ CollisionOracle S H v (H v x)) := by
  classical
  have hbad : ∀ x ∈ (Finset.univ : Finset U) \ S,
      (badSeeds S H x).card ≤ S.card * c := by
    intro x hx
    apply badSeeds_card_le_pair_budget S H x c
    intro y hy
    exact hpair x (Finset.mem_sdiff.mp hx).2 y hy
  obtain ⟨v, hv⟩ := exists_seed_avoiding_bad_sets
    ((Finset.univ : Finset U) \ S)
    (badSeeds S H) (S.card * c) hbad hbudget
  refine ⟨v, ?_⟩
  intro x
  constructor
  · intro hx
    exact positive_maps_into_collision_oracle S H v hx
  · intro horacle
    by_contra hx
    have hxout : x ∈ (Finset.univ : Finset U) \ S := by
      simp [hx]
    have hvnot := hv x hxout
    have hvmem : v ∈ badSeeds S H x :=
      (collision_oracle_iff_mem_badSeeds S H x v).mp horacle
    exact hvnot hvmem

/-- Scalar shadow of the circuit-composition consequence: if source cost is at
most oracle cost plus hash/composition cost, the oracle must inherit the
remaining source cost. -/
theorem collision_oracle_cost_lower_bound
    (sourceCost oracleCost hashCost overhead : ℕ)
    (hcompose : sourceCost ≤ oracleCost + hashCost + overhead) :
    sourceCost - (hashCost + overhead) ≤ oracleCost := by
  omega

#print axioms positive_maps_into_collision_oracle
#print axioms mem_pairBadSeeds_iff
#print axioms mem_badSeeds_iff
#print axioms collision_oracle_iff_mem_badSeeds
#print axioms badSeeds_card_le_pair_budget
#print axioms exists_seed_avoiding_bad_sets
#print axioms exists_exact_collision_seed_of_pair_budget
#print axioms collision_oracle_cost_lower_bound

end Round214PNP
end Millennium
