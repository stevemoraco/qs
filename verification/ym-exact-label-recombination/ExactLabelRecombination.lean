import Mathlib

namespace Millennium.YangMills

/-!
# Exact label recombination core

Finite algebra for the Kirk-v4 transition/outer-label audit.

The source uses a four-way pointwise partition of unity only as temporary
absolute-value bookkeeping and later recombines the labels exactly.  The
finite theorem below records the load-bearing algebra: if the four labels sum
to one, multiplying the same underlying factor by the four labels and summing
recovers that factor exactly.  No analyticity of the individual labels is
needed for this identity.

This theorem does **not** prove that Kirk's labelled histories are all literal
copies of one common analytic factor, does not prove the exact-history
recombination theorem, does not prove post-compact optical holomorphy, Theorem
6.43, Osterwalder--Schrader reconstruction, the Yang--Mills mass gap, or a Clay
theorem.
-/

/-- A four-label partition of unity recombines an underlying factor exactly. -/
theorem four_label_partition_recombines
    {R : Type*} [CommSemiring R]
    (chiIn chiCurv chiCol chiOut f : R)
    (hsum : chiIn + chiCurv + chiCol + chiOut = 1) :
    chiIn * f + chiCurv * f + chiCol * f + chiOut * f = f := by
  calc
    chiIn * f + chiCurv * f + chiCol * f + chiOut * f =
        (chiIn + chiCurv + chiCol + chiOut) * f := by ring
    _ = 1 * f := by rw [hsum]
    _ = f := one_mul f

/-- Pointwise functional form of `four_label_partition_recombines`. -/
theorem four_label_partition_recombines_pointwise
    {X R : Type*} [CommSemiring R]
    (chiIn chiCurv chiCol chiOut f : X → R)
    (hsum : ∀ x, chiIn x + chiCurv x + chiCol x + chiOut x = 1) :
    ∀ x,
      chiIn x * f x + chiCurv x * f x + chiCol x * f x + chiOut x * f x = f x := by
  intro x
  exact four_label_partition_recombines
    (chiIn x) (chiCurv x) (chiCol x) (chiOut x) (f x) (hsum x)

#print axioms four_label_partition_recombines
#print axioms four_label_partition_recombines_pointwise

end Millennium.YangMills
