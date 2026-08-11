import Mathlib

/-!
# BSD core-vertex residual primitivity: finite algebra bank

This file formalizes only elementary algebra used in the BSD braid:

* nonzero elements generate a one-dimensional residue field after a basis is
  chosen;
* a linear equivalence reflects residual nonvanishing;
* finite DVR levels truncate valuation depth;
* a level above an a priori valuation bound recovers the exact order; and
* the refined-Kurihara valuation identities algebraically imply the rank-zero
  p-BSD valuation identity once the p-primary torsion term vanishes.

It does not formalize Selmer complexes, Stark systems, Euler systems,
Iwasawa main conjectures, or the Birch--Swinnerton-Dyer conjecture.
-/

namespace MillenniumBSD
namespace CoreVertexPrimitivity

/-- The set of scalar multiples of `a`.  After choosing a basis of a
rank-one line, this is the corresponding cyclic submodule. -/
def principalMultiples {R : Type*} [Mul R] (a : R) : Set R :=
  {x | ∃ r : R, x = r * a}

/-- A nonzero scalar generates the whole one-dimensional vector space. -/
theorem field_nonzero_principalMultiples_eq_univ
    {F : Type*} [Field F] {a : F} (ha : a ≠ 0) :
    principalMultiples a = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨x * a⁻¹, ?_⟩
    simp [mul_assoc, ha]

/-- Conversely, a scalar whose multiples fill the residue field is nonzero. -/
theorem field_principalMultiples_eq_univ_iff_ne_zero
    {F : Type*} [Field F] (a : F) :
    principalMultiples a = Set.univ ↔ a ≠ 0 := by
  constructor
  · intro h ha
    have hmem : (1 : F) ∈ principalMultiples a := by
      rw [h]
      trivial
    rcases hmem with ⟨r, hr⟩
    have hone : (1 : F) = 0 := by
      calc
        (1 : F) = r * a := hr
        _ = 0 := by simp [ha]
    exact one_ne_zero hone
  · exact field_nonzero_principalMultiples_eq_univ

/-- A linear equivalence reflects whether a residual component vanishes. -/
theorem linearEquiv_nonzero_iff
    {F D C : Type*} [Field F]
    [AddCommGroup D] [Module F D]
    [AddCommGroup C] [Module F C]
    (ev : D ≃ₗ[F] C) (x : D) :
    ev x ≠ 0 ↔ x ≠ 0 := by
  constructor
  · intro hev hx
    apply hev
    simp [hx]
  · intro hx hev
    apply hx
    apply ev.injective
    simpa using hev

/-- The valuation depth visible modulo a level `n`. -/
def truncatedOrder (n a : ℕ) : ℕ := min a n

/-- Orders below the finite level remain visible. -/
theorem truncatedOrder_eq_self_of_lt
    {n a : ℕ} (ha : a < n) :
    truncatedOrder n a = a := by
  simp [truncatedOrder, Nat.min_eq_left (Nat.le_of_lt ha)]

/-- Every order at least `n` collapses to the same depth at level `n`. -/
theorem truncatedOrder_eq_level_of_le
    {n a : ℕ} (ha : n ≤ a) :
    truncatedOrder n a = n := by
  simp [truncatedOrder, Nat.min_eq_right ha]

/-- Finite reduction cannot distinguish any two orders that are both at
least the reduction level. -/
theorem deep_orders_are_indistinguishable
    {n a b : ℕ} (ha : n ≤ a) (hb : n ≤ b) :
    truncatedOrder n a = truncatedOrder n b := by
  rw [truncatedOrder_eq_level_of_le ha, truncatedOrder_eq_level_of_le hb]

/-- If both orders are still visible, equality of finite reductions recovers
exact equality. -/
theorem visible_equal_truncation_recovers_order
    {n a b : ℕ} (ha : a < n) (hb : b < n)
    (h : truncatedOrder n a = truncatedOrder n b) :
    a = b := by
  simpa [truncatedOrder_eq_self_of_lt ha,
    truncatedOrder_eq_self_of_lt hb] using h

/-- A single level above a known valuation bound is injective on all allowed
orders. -/
theorem bounded_level_recovers_order
    {B a b : ℕ} (ha : a ≤ B) (hb : b ≤ B)
    (h : truncatedOrder (B + 1) a = truncatedOrder (B + 1) b) :
    a = b := by
  apply visible_equal_truncation_recovers_order
      (n := B + 1) (a := a) (b := b)
  · omega
  · omega
  · exact h

/-- Abstract arithmetic identity behind the rank-zero p-BSD corollary:
`sha = L - M`, `M = Tamagawa`, and vanishing p-primary torsion imply the
classical leading-term valuation formula. -/
theorem refined_kurihara_implies_rank_zero_pbsd_valuation
    (lval shaval mval tamval torsval : ℤ)
    (hSha : shaval = lval - mval)
    (hRefined : mval = tamval)
    (hTors : torsval = 0) :
    lval = shaval + tamval - 2 * torsval := by
  omega

/-- Once equality is known outside a finite exceptional set and checked on
that set, it holds at every prime. -/
theorem finite_exception_closure
    {Prime : Type*} (exceptional : Set Prime)
    (analytic actual : Prime → ℤ)
    (hout : ∀ p, p ∉ exceptional → analytic p = actual p)
    (hin : ∀ p, p ∈ exceptional → analytic p = actual p) :
    ∀ p, analytic p = actual p := by
  intro p
  by_cases hp : p ∈ exceptional
  · exact hin p hp
  · exact hout p hp

#print axioms field_nonzero_principalMultiples_eq_univ
#print axioms field_principalMultiples_eq_univ_iff_ne_zero
#print axioms linearEquiv_nonzero_iff
#print axioms truncatedOrder_eq_self_of_lt
#print axioms truncatedOrder_eq_level_of_le
#print axioms deep_orders_are_indistinguishable
#print axioms visible_equal_truncation_recovers_order
#print axioms bounded_level_recovers_order
#print axioms refined_kurihara_implies_rank_zero_pbsd_valuation
#print axioms finite_exception_closure

end CoreVertexPrimitivity
end MillenniumBSD
