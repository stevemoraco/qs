import Mathlib

/-!
# Faizal--Shabir fiber multiplicity firewall

Finite combinatorial shadow of the C245 source audit.

If a coarse polymer with `n` independently optional local decorations has one
fine preimage for every subset of those decorations, then the corresponding
fiber family has exactly `2^n` members.  Since `2^n` is unbounded, no single
raw-cardinality constant can bound all such fibers.

This file does **not** formalize the Faizal--Shabir polymer geometry, the
existence of the optional decorations in their model, the weighted polymer
norm, the RG map, Yang--Mills theory, or any Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirFiberMultiplicityFirewall

/-- Abstract family of optional decorations on `n` sites. -/
def optionalDecorationFamily (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset

/-- There are exactly `2^n` optional-decoration choices. -/
theorem optionalDecorationFamily_card (n : ℕ) :
    (optionalDecorationFamily n).card = 2 ^ n := by
  simp [optionalDecorationFamily]

/-- Elementary growth estimate used to show powers of two outrun any fixed
natural cardinality bound. -/
theorem succ_le_two_pow (n : ℕ) :
    n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        n + 2 ≤ 2 * (n + 1) := by omega
        _ ≤ 2 * (2 ^ n) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by ring

/-- Any proposed fixed natural cardinality bound is beaten by an optional-
decoration family at a sufficiently long coarse path. -/
theorem no_uniform_raw_cardinality_bound (C : ℕ) :
    C < (optionalDecorationFamily (C + 1)).card := by
  rw [optionalDecorationFamily_card]
  have h := succ_le_two_pow (C + 1)
  omega

#print axioms optionalDecorationFamily_card
#print axioms succ_le_two_pow
#print axioms no_uniform_raw_cardinality_bound

end Millennium.YangMills.FaizalShabirFiberMultiplicityFirewall
