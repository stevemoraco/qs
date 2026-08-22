import Mathlib

/-!
# Shared-link blocking generates a genuine boundary interaction

This file formalizes only the finite algebraic countermodel used in Round 201.
It does not formalize a compact gauge group, a heat kernel, an RG transformation,
a continuum limit, or the Yang--Mills Millennium problem.
-/

namespace Millennium
namespace Round201YangMills

/-- After summing one shared two-state link, equal boundary signs have this weight. -/
def sharedSame (a b : ℝ) : ℝ := a ^ 2 + b ^ 2

/-- After summing one shared two-state link, opposite boundary signs have this weight. -/
def sharedMixed (a b : ℝ) : ℝ := 2 * a * b

/-- The determinant of the two-by-two boundary weight is an exact square. -/
theorem shared_link_determinant_identity (a b : ℝ) :
    sharedSame a b * sharedSame a b -
        sharedMixed a b * sharedMixed a b =
      (a ^ 2 - b ^ 2) ^ 2 := by
  simp [sharedSame, sharedMixed]
  ring

/-- Every product weight `f(x) g(y)` has rank-one determinant zero. -/
theorem product_weight_determinant_zero
    (fPlus fMinus gPlus gMinus : ℝ) :
    (fPlus * gPlus) * (fMinus * gMinus) -
        (fPlus * gMinus) * (fMinus * gPlus) = 0 := by
  ring

/-- A nonconstant shared-link weight cannot factor as independent functions
of the two boundary variables. -/
theorem shared_link_weight_not_factorized
    (a b : ℝ) (hne : a ^ 2 ≠ b ^ 2) :
    ¬ ∃ fPlus fMinus gPlus gMinus : ℝ,
        fPlus * gPlus = sharedSame a b ∧
        fPlus * gMinus = sharedMixed a b ∧
        fMinus * gPlus = sharedMixed a b ∧
        fMinus * gMinus = sharedSame a b := by
  rintro ⟨fPlus, fMinus, gPlus, gMinus, hpp, hpm, hmp, hmm⟩
  have hrank :
      sharedSame a b * sharedSame a b -
          sharedMixed a b * sharedMixed a b = 0 := by
    calc
      sharedSame a b * sharedSame a b -
          sharedMixed a b * sharedMixed a b =
        (fPlus * gPlus) * (fMinus * gMinus) -
          (fPlus * gMinus) * (fMinus * gPlus) := by
            rw [hpp, hpm, hmp, hmm]
      _ = 0 := product_weight_determinant_zero
        fPlus fMinus gPlus gMinus
  rw [shared_link_determinant_identity] at hrank
  have hz : a ^ 2 - b ^ 2 = 0 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
  exact hne (sub_eq_zero.mp hz)

/-- Positive unequal plaquette weights meet the nonfactorization hypothesis. -/
theorem positive_unequal_shared_link_weight_not_factorized
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ¬ ∃ fPlus fMinus gPlus gMinus : ℝ,
        fPlus * gPlus = sharedSame a b ∧
        fPlus * gMinus = sharedMixed a b ∧
        fMinus * gPlus = sharedMixed a b ∧
        fMinus * gMinus = sharedSame a b := by
  apply shared_link_weight_not_factorized a b
  intro hsq
  have hsum : 0 < a + b := by linarith
  have hprod : (a - b) * (a + b) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hprod with hdiff | hsumzero
  · exact hab (sub_eq_zero.mp hdiff)
  · linarith

/-- A finite RG history can agree through an arbitrarily prescribed checkpoint
and then have opposite eventual basin-entry behavior. This is only a discrete
information countermodel, not a statement about the actual Yang--Mills flow. -/
theorem finite_prefix_does_not_determine_eventual_entry (N : ℕ) :
    ∃ enters avoids : ℕ → ℕ,
      (∀ n ≤ N, enters n = avoids n) ∧
      (∃ n, enters n = 1) ∧
      (∀ n, avoids n ≠ 1) := by
  refine ⟨fun n => if n ≤ N then 0 else 1, fun _ => 0, ?_, ?_, ?_⟩
  · intro n hn
    simp [hn]
  · refine ⟨N + 1, ?_⟩
    simp
  · intro n
    norm_num

#print axioms shared_link_determinant_identity
#print axioms product_weight_determinant_zero
#print axioms shared_link_weight_not_factorized
#print axioms positive_unequal_shared_link_weight_not_factorized
#print axioms finite_prefix_does_not_determine_eventual_entry

end Round201YangMills
end Millennium
