import Mathlib

open scoped BigOperators

namespace Millennium.YM.LiuHarmonicTail

/-- A block of `L` copies of `1/(2L)` has exact mass `1/2`. -/
theorem banker_constant_dyadic_block_sum
    (L : ℕ) (hL : 0 < L) :
    (∑ _i : Fin L, (1 / (2 * (L : ℚ)) : ℚ)) = (1 / 2 : ℚ) := by
  have hLq : (L : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hL
  rw [Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hLq]

/--
BANKER: if each entry of a dyadic block is at least `1/(2L)`, then the
whole block has mass at least `1/2`.
-/
theorem banker_dyadic_block_lower
    (L : ℕ) (hL : 0 < L)
    (a : Fin L → ℚ)
    (h : ∀ i, (1 / (2 * (L : ℚ)) : ℚ) ≤ a i) :
    (1 / 2 : ℚ) ≤ ∑ i, a i := by
  have hsum :
      (∑ i : Fin L, (1 / (2 * (L : ℚ)) : ℚ)) ≤ ∑ i, a i := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact h i
  rw [banker_constant_dyadic_block_sum L hL] at hsum
  exact hsum

/--
CRITIC: the constant comparison block itself already costs exactly `1/2`;
it cannot be treated as a vanishing tail.
-/
theorem critic_fixed_half_block_cost
    (L : ℕ) (hL : 0 < L) :
    ∃ a : Fin L → ℚ,
      (∀ i, (1 / (2 * (L : ℚ)) : ℚ) ≤ a i) ∧
      (∑ i, a i) = (1 / 2 : ℚ) := by
  refine ⟨fun _ => (1 / (2 * (L : ℚ)) : ℚ), ?_, ?_⟩
  · intro i
    exact le_rfl
  · exact banker_constant_dyadic_block_sum L hL

/--
CLEANER: a family with a `1/2` lower bound on every positive dyadic block
cannot have even one certified block below `1/2`.
-/
theorem cleaner_no_vanishing_tail_certificate
    (tail : ℕ → ℚ)
    (hblock : ∀ L : ℕ, 0 < L → (1 / 2 : ℚ) ≤ tail L) :
    ¬ ∃ L : ℕ, 0 < L ∧ tail L < (1 / 2 : ℚ) := by
  rintro ⟨L, hL, hsmall⟩
  exact (not_lt_of_ge (hblock L hL)) hsmall

#print axioms banker_constant_dyadic_block_sum
#print axioms banker_dyadic_block_lower
#print axioms critic_fixed_half_block_cost
#print axioms cleaner_no_vanishing_tail_certificate

end Millennium.YM.LiuHarmonicTail
