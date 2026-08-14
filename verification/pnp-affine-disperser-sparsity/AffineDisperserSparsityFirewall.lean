import Mathlib

/-!
# P versus NP: affine-disperser sparsity firewall

Finite combinatorial core only.

Write an `(r+d)`-bit input as a pair `(prefix,suffix)`.  The `2^r`
prefix fibres are pairwise disjoint coordinate `d`-flats.  If every such flat
contains a positive input, choosing one positive completion per prefix gives an
injection from the `r`-bit prefix cube into the positive support.  The same
statement holds for the negative support.

Consequently any Boolean function that is nonconstant on every coordinate
`d`-flat has at least `2^r` positives and at least `2^r` negatives.  An affine
disperser for dimension `d` satisfies this coordinate-flat condition after any
fixed coordinate splitting, so the finite theorem is the exact cardinality
shadow used in the human sparsity audit.

This file defines no circuits, affine dispersers, NP, P, hardness magnification,
or P-vs-NP theorem.
-/

namespace Millennium.PNP.AffineDisperserSparsityFirewall

abbrev Bits (n : ℕ) := Fin n → Bool
abbrev SplitInput (r d : ℕ) := Bits r × Bits d

abbrev Positive {r d : ℕ} (f : SplitInput r d → Bool) :=
  {x : SplitInput r d // f x = true}

abbrev Negative {r d : ℕ} (f : SplitInput r d → Bool) :=
  {x : SplitInput r d // f x = false}

/-- If every prefix fibre contains a positive point, then the positive support
contains at least one distinct point for each prefix. -/
theorem coordinate_flat_positive_support_lower_bound
    {r d : ℕ}
    (f : SplitInput r d → Bool)
    (hhit : ∀ p : Bits r, ∃ s : Bits d, f (p, s) = true) :
    2 ^ r ≤ Fintype.card (Positive f) := by
  classical
  let pick : Bits r → Positive f := fun p =>
    ⟨(p, Classical.choose (hhit p)), Classical.choose_spec (hhit p)⟩
  have hinj : Function.Injective pick := by
    intro p q hpq
    have hval : (pick p : SplitInput r d) = (pick q : SplitInput r d) :=
      congrArg Subtype.val hpq
    exact congrArg Prod.fst hval
  have hcard : Fintype.card (Bits r) ≤ Fintype.card (Positive f) :=
    Fintype.card_le_of_injective pick hinj
  simpa [Bits] using hcard

/-- Symmetric support bound for zeroes. -/
theorem coordinate_flat_negative_support_lower_bound
    {r d : ℕ}
    (f : SplitInput r d → Bool)
    (hhit : ∀ p : Bits r, ∃ s : Bits d, f (p, s) = false) :
    2 ^ r ≤ Fintype.card (Negative f) := by
  classical
  let pick : Bits r → Negative f := fun p =>
    ⟨(p, Classical.choose (hhit p)), Classical.choose_spec (hhit p)⟩
  have hinj : Function.Injective pick := by
    intro p q hpq
    have hval : (pick p : SplitInput r d) = (pick q : SplitInput r d) :=
      congrArg Subtype.val hpq
    exact congrArg Prod.fst hval
  have hcard : Fintype.card (Bits r) ≤ Fintype.card (Negative f) :=
    Fintype.card_le_of_injective pick hinj
  simpa [Bits] using hcard

/-- If every coordinate `d`-flat is mixed, both label supports have cardinality
at least `2^r`. -/
theorem coordinate_flat_mixing_forces_two_sided_support
    {r d : ℕ}
    (f : SplitInput r d → Bool)
    (hmix : ∀ p : Bits r,
      (∃ s : Bits d, f (p, s) = true) ∧
      (∃ s : Bits d, f (p, s) = false)) :
    (2 ^ r ≤ Fintype.card (Positive f)) ∧
    (2 ^ r ≤ Fintype.card (Negative f)) := by
  constructor
  · apply coordinate_flat_positive_support_lower_bound f
    intro p
    exact (hmix p).1
  · apply coordinate_flat_negative_support_lower_bound f
    intro p
    exact (hmix p).2

/-- A positive support smaller than the number of prefix fibres precludes even
the weaker property that every coordinate flat contains one positive point. -/
theorem sparse_positive_support_precludes_full_flat_hitting
    {r d : ℕ}
    (f : SplitInput r d → Bool)
    (hsmall : Fintype.card (Positive f) < 2 ^ r) :
    ¬ (∀ p : Bits r, ∃ s : Bits d, f (p, s) = true) := by
  intro hhit
  have hlower := coordinate_flat_positive_support_lower_bound f hhit
  omega

/-- Hence support below `2^r` also precludes coordinate-flat mixing. -/
theorem sparse_positive_support_precludes_coordinate_flat_mixing
    {r d : ℕ}
    (f : SplitInput r d → Bool)
    (hsmall : Fintype.card (Positive f) < 2 ^ r) :
    ¬ (∀ p : Bits r,
      (∃ s : Bits d, f (p, s) = true) ∧
      (∃ s : Bits d, f (p, s) = false)) := by
  intro hmix
  have hlower := (coordinate_flat_mixing_forces_two_sided_support f hmix).1
  omega

/-- Symmetric sparse-negative obstruction. -/
theorem sparse_negative_support_precludes_coordinate_flat_mixing
    {r d : ℕ}
    (f : SplitInput r d → Bool)
    (hsmall : Fintype.card (Negative f) < 2 ^ r) :
    ¬ (∀ p : Bits r,
      (∃ s : Bits d, f (p, s) = true) ∧
      (∃ s : Bits d, f (p, s) = false)) := by
  intro hmix
  have hlower := (coordinate_flat_mixing_forces_two_sided_support f hmix).2
  omega

#print axioms coordinate_flat_positive_support_lower_bound
#print axioms coordinate_flat_negative_support_lower_bound
#print axioms coordinate_flat_mixing_forces_two_sided_support
#print axioms sparse_positive_support_precludes_full_flat_hitting
#print axioms sparse_positive_support_precludes_coordinate_flat_mixing
#print axioms sparse_negative_support_precludes_coordinate_flat_mixing

end Millennium.PNP.AffineDisperserSparsityFirewall
