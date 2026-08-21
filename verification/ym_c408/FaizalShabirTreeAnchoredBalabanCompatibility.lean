import Mathlib

/-!
# C408 finite tree-gauge compatibility firewall

This file formalizes only the finite algebraic core of the C408 repair.

If left/right tree connector holonomies are the identity, each anchored path
holonomy equals its straight middle holonomy. Consequently *any* averaging
functional applied to the anchored family gives the same output as on the
straight family. The additive/vector-space shadow gives the corresponding
arithmetic-mean statement.

It does **not** formalize lattice path geometry, tree gauge fixing, matrix polar
decomposition, determinant branches, Balaban's source theorem, RG transport,
or Yang--Mills.
-/

namespace Millennium.YangMills.FaizalShabirTreeAnchoredBalabanCompatibility

open scoped BigOperators

section Group

variable {ι G : Type*} [Group G]

/-- Identity-valued tree connectors make every anchored group path equal to
its straight middle path. -/
theorem anchoredFamily_eq_straight
    (left straight right : ι → G)
    (hleft : ∀ i, left i = 1)
    (hright : ∀ i, right i = 1) :
    (fun i => left i * straight i * (right i)⁻¹) = straight := by
  funext i
  simp [hleft i, hright i]

/-- Once the anchored and straight path families agree pointwise, an arbitrary
(possibly nonlinear) group-valued averaging functional returns the same value.
This is the exact finite consumer used for the polar/group-average layer. -/
theorem arbitraryAverage_anchored_eq_straight
    (avg : (ι → G) → G)
    (left straight right : ι → G)
    (hleft : ∀ i, left i = 1)
    (hright : ∀ i, right i = 1) :
    avg (fun i => left i * straight i * (right i)⁻¹) = avg straight := by
  exact congrArg avg
    (anchoredFamily_eq_straight left straight right hleft hright)

end Group

section AdditivePointwise

variable {ι V : Type*} [AddCommGroup V]

/-- Zero additive tree connectors make every anchored additive path equal to
its straight middle path. -/
theorem anchoredAdditiveFamily_eq_straight
    (left straight right : ι → V)
    (hleft : ∀ i, left i = 0)
    (hright : ∀ i, right i = 0) :
    (fun i => left i + straight i + right i) = straight := by
  funext i
  simp [hleft i, hright i]

end AdditivePointwise

section AdditiveMean

variable {ι V : Type*} [Fintype ι]
variable [AddCommGroup V] [Module ℝ V]

/-- Arithmetic mean of a finite vector-valued family. The definition is useful
as the additive first-order shadow of both the FS path average and Balaban's
linear averaging operator. -/
noncomputable def arithmeticMean (f : ι → V) : V :=
  ((Fintype.card ι : ℝ)⁻¹) • ∑ i, f i

/-- The anchored arithmetic mean equals the straight arithmetic mean whenever
the additive connector contributions vanish. -/
theorem arithmeticMean_anchored_eq_straight
    (left straight right : ι → V)
    (hleft : ∀ i, left i = 0)
    (hright : ∀ i, right i = 0) :
    arithmeticMean (fun i => left i + straight i + right i) =
      arithmeticMean straight := by
  rw [anchoredAdditiveFamily_eq_straight left straight right hleft hright]

end AdditiveMean

#print axioms anchoredFamily_eq_straight
#print axioms arbitraryAverage_anchored_eq_straight
#print axioms anchoredAdditiveFamily_eq_straight
#print axioms arithmeticMean_anchored_eq_straight

end Millennium.YangMills.FaizalShabirTreeAnchoredBalabanCompatibility
