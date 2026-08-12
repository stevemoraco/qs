import Mathlib

/-!
# P versus NP marker route: finite DAG-unfolding recurrence core

Honesty status: this file formalizes only the natural-number recurrences for an
abstract diamond chain: one excess-fanout event per level and doubling of the
fully unfolded base-copy count.

It does not formalize Boolean circuits, formula unfolding, biclique partitions,
the marker language, probabilistic error, hardness magnification, NP, or
`P != NP`.
-/

namespace MillenniumBraid
namespace PNPDAGUnfoldingFinite

def excess (d : ℕ) : ℕ := d

def copies (d : ℕ) : ℕ := 2 ^ d

theorem excess_succ (d : ℕ) :
    excess (d + 1) = excess d + 1 := by
  simp [excess]

theorem copies_succ (d : ℕ) :
    copies (d + 1) = 2 * copies d := by
  simp [copies, pow_succ]
  omega

theorem copies_eq_two_pow_excess (d : ℕ) :
    copies d = 2 ^ excess d := by
  rfl

theorem depth_twenty_amplification :
    copies 20 = 1048576 ∧ excess 20 = 20 ∧
      1000 * (excess 20 + 1) < copies 20 := by
  norm_num [copies, excess]

theorem copies_dominate_linear (d : ℕ) :
    d + 1 ≤ copies d := by
  induction d with
  | zero => simp [copies]
  | succ d ih =>
      rw [copies_succ]
      omega

theorem iterated_copy_product (d q : ℕ) :
    (copies d) ^ q = 2 ^ (d * q) := by
  simp [copies, pow_mul]

#print axioms excess_succ
#print axioms copies_succ
#print axioms copies_eq_two_pow_excess
#print axioms depth_twenty_amplification
#print axioms copies_dominate_linear
#print axioms iterated_copy_product

end PNPDAGUnfoldingFinite
end MillenniumBraid
