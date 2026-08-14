import PNPFiniteSeedDerandomization

/-!
# Exact derandomization for the n-bit UNIT predicate at error 2^{-n}

The `n` unit vectors form a set of cardinality `n` inside the `2^n` Boolean
vectors.  For `n>0`, the false domain therefore has cardinality
`2^n-n < 2^n`.

If a finite uniform seed family has perfect completeness on every unit vector
and, for every non-unit vector, its false-positive seed count times `2^n` is
at most the total number of seeds, then one seed is exact on the entire UNIT
truth table.  Hardwiring that seed adds no circuit gates.

This is a finite theorem.  It does not assert that any particular published
hardness-magnification premise uses exactly these quantifiers or this error
normalization; that source instantiation is a separate theorem.
-/

namespace PNPUnitExactSeed

abbrev BitVec (n : ℕ) := Fin n → Bool

/-- The standard Boolean unit vector at coordinate `i`. -/
def unitVec {n : ℕ} (i : Fin n) : BitVec n :=
  fun j => if j = i then true else false

/-- Distinct coordinates give distinct unit vectors. -/
theorem unitVec_injective {n : ℕ} :
    Function.Injective (@unitVec n) := by
  intro i j hij
  by_contra hne
  have hcoord := congrFun hij i
  simp [unitVec, hne] at hcoord

/-- The finite set of all unit vectors. -/
def unitSet (n : ℕ) : Finset (BitVec n) := by
  classical
  exact Finset.univ.image unitVec

/-- There are exactly `n` Boolean unit vectors. -/
theorem card_unitSet (n : ℕ) :
    (unitSet n).card = n := by
  classical
  unfold unitSet
  rw [Finset.card_image_iff.mpr]
  · simp
  · exact unitVec_injective.injOn

/-- The complement of the unit vectors in the full Boolean cube. -/
def nonUnitSet (n : ℕ) : Finset (BitVec n) := by
  classical
  exact Finset.univ \ unitSet n

/-- Exact false-domain cardinality for UNIT. -/
theorem card_nonUnitSet (n : ℕ) :
    (nonUnitSet n).card = (2 : ℕ) ^ n - n := by
  classical
  have hsub : unitSet n ⊆ (Finset.univ : Finset (BitVec n)) :=
    Finset.subset_univ _
  unfold nonUnitSet
  rw [Finset.card_sdiff hsub, card_unitSet]
  simp [BitVec]

/-- Elementary bound needed to make the complement cardinality strict. -/
theorem nat_le_two_pow : ∀ n : ℕ, n ≤ (2 : ℕ) ^ n
  | 0 => by simp
  | n + 1 => by
      have ih := nat_le_two_pow n
      have hp : 1 ≤ (2 : ℕ) ^ n := by positivity
      calc
        n + 1 ≤ (2 : ℕ) ^ n + 1 := Nat.add_le_add_right ih 1
        _ ≤ (2 : ℕ) ^ n + (2 : ℕ) ^ n :=
          Nat.add_le_add_left hp ((2 : ℕ) ^ n)
        _ = (2 : ℕ) ^ (n + 1) := by
          rw [pow_succ]
          omega

/-- For every positive input length, the false UNIT domain has strictly fewer
than `2^n` elements. -/
theorem card_nonUnitSet_lt_pow
    (n : ℕ) (hn : 0 < n) :
    (nonUnitSet n).card < (2 : ℕ) ^ n := by
  rw [card_nonUnitSet]
  have hle := nat_le_two_pow n
  have hp : 0 < (2 : ℕ) ^ n := by positivity
  omega

/-- General scaled-column double counting.  If the false-domain cardinality
is smaller than the probability denominator `D`, and every pointwise bad-seed
count is at most `|R|/D` in the exact cross-multiplied sense, one seed has no
false positives. -/
theorem exists_exact_seed_of_scaled_columns
    {R X : Type*}
    [Fintype R] [Fintype X]
    (D : ℕ)
    (accept : R → X → Prop)
    (hR : 0 < Fintype.card R)
    (hD : 0 < D)
    (hX : Fintype.card X < D)
    (hcol : ∀ x,
      (∑ r, if accept r x then 1 else 0) * D ≤ Fintype.card R) :
    ∃ r, ∀ x, ¬ accept r x := by
  classical
  by_contra hnone
  push_neg at hnone
  let bad : R → X → ℕ := fun r x => if accept r x then 1 else 0
  have hrow : ∀ r, 1 ≤ ∑ x, bad r x := by
    intro r
    obtain ⟨x, hx⟩ := hnone r
    have hone : 1 ≤ bad r x := by simp [bad, hx]
    have hterm : bad r x ≤ ∑ x', bad r x' := by
      exact Finset.single_le_sum
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ x)
    exact hone.trans hterm
  have hlower : Fintype.card R ≤ ∑ r, ∑ x, bad r x := by
    calc
      Fintype.card R = ∑ _r : R, 1 := by simp
      _ ≤ ∑ r, ∑ x, bad r x := by
        apply Finset.sum_le_sum
        intro r hr
        exact hrow r
  have hswap : (∑ r, ∑ x, bad r x) = ∑ x, ∑ r, bad r x := by
    simpa using (Fintype.sum_comm bad)
  have hscaledUpper :
      (∑ x, ∑ r, bad r x) * D ≤
        Fintype.card X * Fintype.card R := by
    calc
      (∑ x, ∑ r, bad r x) * D
          = ∑ x, ((∑ r, bad r x) * D) := by
              rw [Finset.sum_mul]
      _ ≤ ∑ _x : X, Fintype.card R := by
        apply Finset.sum_le_sum
        intro x hx
        simpa [bad] using hcol x
      _ = Fintype.card X * Fintype.card R := by simp
  have hlowerScaled :
      Fintype.card R * D ≤ (∑ x, ∑ r, bad r x) * D := by
    apply Nat.mul_le_mul_right D
    calc
      Fintype.card R ≤ ∑ r, ∑ x, bad r x := hlower
      _ = ∑ x, ∑ r, bad r x := hswap
  have hdomainScaled :
      Fintype.card X * Fintype.card R < D * Fintype.card R :=
    Nat.mul_lt_mul_of_pos_right hX hR
  have hcontra : Fintype.card R * D < Fintype.card R * D := by
    calc
      Fintype.card R * D
          ≤ (∑ x, ∑ r, bad r x) * D := hlowerScaled
      _ ≤ Fintype.card X * Fintype.card R := hscaledUpper
      _ < D * Fintype.card R := hdomainScaled
      _ = Fintype.card R * D := by omega
  exact (Nat.lt_irrefl _ hcontra)

/-- Exact UNIT derandomization at pointwise false-positive probability at most
`2^{-n}` for a finite uniform seed family. -/
theorem unit_exact_seed
    (n N : ℕ)
    (hn : 0 < n)
    (hN : 0 < N)
    (accept : Fin N → BitVec n → Prop)
    (hcomplete : ∀ r i, accept r (unitVec i))
    (hpointwise : ∀ x, x ∈ nonUnitSet n →
      (∑ r, if accept r x then 1 else 0) * (2 : ℕ) ^ n ≤ N) :
    ∃ r,
      (∀ i, accept r (unitVec i)) ∧
      (∀ x, x ∈ nonUnitSet n → ¬ accept r x) := by
  classical
  let FalseInput := {x : BitVec n // x ∈ nonUnitSet n}
  have hFalseCard : Fintype.card FalseInput < (2 : ℕ) ^ n := by
    simpa [FalseInput] using card_nonUnitSet_lt_pow n hn
  have hpow : 0 < (2 : ℕ) ^ n := by positivity
  have hcol : ∀ x : FalseInput,
      (∑ r : Fin N, if accept r x.1 then 1 else 0) * (2 : ℕ) ^ n ≤
        Fintype.card (Fin N) := by
    intro x
    simpa using hpointwise x.1 x.2
  obtain ⟨r, hr⟩ := exists_exact_seed_of_scaled_columns
    ((2 : ℕ) ^ n)
    (fun r (x : FalseInput) => accept r x.1)
    (by simpa using hN)
    hpow hFalseCard hcol
  refine ⟨r, hcomplete r, ?_⟩
  intro x hx
  exact hr ⟨x, hx⟩

#print axioms unitVec_injective
#print axioms card_unitSet
#print axioms card_nonUnitSet
#print axioms nat_le_two_pow
#print axioms card_nonUnitSet_lt_pow
#print axioms exists_exact_seed_of_scaled_columns
#print axioms unit_exact_seed

end PNPUnitExactSeed
