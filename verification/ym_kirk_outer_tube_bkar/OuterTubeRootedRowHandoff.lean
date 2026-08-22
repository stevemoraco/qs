import Mathlib

namespace Millennium.YangMills

/-!
# Outer-tube rooted-row handoff

Finite order/row algebra for the current compact-to-BKAR source audit.

The analytic application starts from one uniform `q = 0` post-compact activity
row on a fixed outer optical tube.  Banach-valued Cauchy on a fixed smaller
tube supplies a pointwise derivative cost at every order.  A fixed coefficient
norm map, a fixed output-recertification map, and a fixed support-incidence
loss may then be applied *inside the rooted sum* without creating a
regulator-dependent constant.

This file formalizes only that finite rooted-sum bookkeeping.  It does not
formalize Banach holomorphy, Cauchy's theorem, Kirk's post-compact activity row,
the replica--BKAR theorem, Osterwalder--Schrader reconstruction, Yang--Mills, a
mass gap, or a Clay theorem.
-/

open scoped BigOperators

/-- A four-mark maximum really contains its zeroth-order member.  This is the
finite shadow of reading the `r = 0` member of a printed `Dζ≤3` row. -/
theorem zeroth_mark_le_four_mark_max
    (m0 m1 m2 m3 M : ℝ)
    (hrow : max m0 (max m1 (max m2 m3)) ≤ M) :
    m0 ≤ M := by
  exact (le_max_left m0 (max m1 (max m2 m3))).trans hrow

/-- Any fixed pointwise norm conversion transfers through a rooted activity
row with exactly the same fixed multiplier. -/
theorem fixed_pointwise_map_transfers_rooted_row
    {A P : Type*} [DecidableEq A] [DecidableEq P]
    (activities : Finset A)
    (support : A → Finset P)
    (outer target : A → ℝ)
    (K eta : ℝ)
    (hK : 0 ≤ K)
    (hmap : ∀ a ∈ activities, target a ≤ K * outer a)
    (hrow : ∀ p,
      (∑ a ∈ activities, if p ∈ support a then outer a else 0) ≤ eta) :
    ∀ p,
      (∑ a ∈ activities, if p ∈ support a then target a else 0) ≤ K * eta := by
  intro p
  calc
    (∑ a ∈ activities, if p ∈ support a then target a else 0) ≤
        ∑ a ∈ activities, if p ∈ support a then K * outer a else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases hp : p ∈ support a
      · simpa [hp] using hmap a ha
      · simp [hp]
    _ = K * (∑ a ∈ activities, if p ∈ support a then outer a else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hp : p ∈ support a
      · simp [hp]
      · simp [hp]
    _ ≤ K * eta := mul_le_mul_of_nonneg_left (hrow p) hK

/-- Once Cauchy has produced a fixed order-dependent pointwise multiplier, the
entire derivative row inherits that multiplier.  No derivative order is
confused with a finite list of pre-existing passive marks. -/
theorem fixed_cauchy_cost_transfers_every_rooted_row
    {A P : Type*} [DecidableEq A] [DecidableEq P]
    (activities : Finset A)
    (support : A → Finset P)
    (outer : A → ℝ)
    (deriv : ℕ → A → ℝ)
    (cost : ℕ → ℝ)
    (eta : ℝ)
    (hcost : ∀ q, 0 ≤ cost q)
    (hcauchy : ∀ q a, a ∈ activities → deriv q a ≤ cost q * outer a)
    (hrow : ∀ p,
      (∑ a ∈ activities, if p ∈ support a then outer a else 0) ≤ eta) :
    ∀ q p,
      (∑ a ∈ activities, if p ∈ support a then deriv q a else 0) ≤
        cost q * eta := by
  intro q
  exact fixed_pointwise_map_transfers_rooted_row
    activities support outer (deriv q) (cost q) eta (hcost q)
    (fun a ha => hcauchy q a ha) hrow

/-- A fixed loss from a strong support weight to a weaker support weight,
including a fixed incidence multiplicity, transfers through the rooted row.

In the source application the pointwise hypothesis is obtained by spending a
fixed positive amount of the compact diameter exponent to dominate a fixed
polynomial support/incidence factor. -/
theorem fixed_support_loss_transfers_rooted_row
    {A P : Type*} [DecidableEq A] [DecidableEq P]
    (activities : Finset A)
    (support : A → Finset P)
    (strongWeight weakWeight incidence mass : A → ℝ)
    (Ksupport eta : ℝ)
    (hKsupport : 0 ≤ Ksupport)
    (hmass : ∀ a ∈ activities, 0 ≤ mass a)
    (hweight : ∀ a ∈ activities,
      weakWeight a * incidence a ≤ Ksupport * strongWeight a)
    (hrow : ∀ p,
      (∑ a ∈ activities,
        if p ∈ support a then strongWeight a * mass a else 0) ≤ eta) :
    ∀ p,
      (∑ a ∈ activities,
        if p ∈ support a then weakWeight a * incidence a * mass a else 0) ≤
          Ksupport * eta := by
  apply fixed_pointwise_map_transfers_rooted_row
    activities support
    (fun a => strongWeight a * mass a)
    (fun a => weakWeight a * incidence a * mass a)
    Ksupport eta hKsupport
  · intro a ha
    have hmul := mul_le_mul_of_nonneg_right (hweight a ha) (hmass a ha)
    nlinarith
  · exact hrow

/-- One outer-tube row pays a fixed coefficient-norm handoff, the derived
regulator-allocation row, and the parent-normalized tree row.  Every constant
is chosen before the regulator/separation parameter. -/
theorem one_outer_row_pays_fixed_bkar_handoff
    {A P : Type*} [DecidableEq A] [DecidableEq P]
    (activities : Finset A)
    (support : A → Finset P)
    (outer species allocation tree : A → ℝ)
    (Kmap Crec Ctree eta : ℝ)
    (hKmap : 0 ≤ Kmap)
    (hCrec : 0 ≤ Crec)
    (hCtree : 0 ≤ Ctree)
    (hspecies : ∀ a ∈ activities, species a ≤ Kmap * outer a)
    (halloc : ∀ a ∈ activities, allocation a ≤ Crec * species a)
    (htree : ∀ a ∈ activities, tree a ≤ Ctree * species a)
    (hrow : ∀ p,
      (∑ a ∈ activities, if p ∈ support a then outer a else 0) ≤ eta) :
    (∀ p,
      (∑ a ∈ activities, if p ∈ support a then species a else 0) ≤
        Kmap * eta) ∧
    (∀ p,
      (∑ a ∈ activities, if p ∈ support a then allocation a else 0) ≤
        (Crec * Kmap) * eta) ∧
    (∀ p,
      (∑ a ∈ activities, if p ∈ support a then tree a else 0) ≤
        (Ctree * Kmap) * eta) := by
  have hspeciesRow := fixed_pointwise_map_transfers_rooted_row
    activities support outer species Kmap eta hKmap hspecies hrow
  have hallocMap : ∀ a ∈ activities,
      allocation a ≤ (Crec * Kmap) * outer a := by
    intro a ha
    calc
      allocation a ≤ Crec * species a := halloc a ha
      _ ≤ Crec * (Kmap * outer a) :=
        mul_le_mul_of_nonneg_left (hspecies a ha) hCrec
      _ = (Crec * Kmap) * outer a := by ring
  have htreeMap : ∀ a ∈ activities,
      tree a ≤ (Ctree * Kmap) * outer a := by
    intro a ha
    calc
      tree a ≤ Ctree * species a := htree a ha
      _ ≤ Ctree * (Kmap * outer a) :=
        mul_le_mul_of_nonneg_left (hspecies a ha) hCtree
      _ = (Ctree * Kmap) * outer a := by ring
  have hallocRow := fixed_pointwise_map_transfers_rooted_row
    activities support outer allocation (Crec * Kmap) eta
    (mul_nonneg hCrec hKmap) hallocMap hrow
  have htreeRow := fixed_pointwise_map_transfers_rooted_row
    activities support outer tree (Ctree * Kmap) eta
    (mul_nonneg hCtree hKmap) htreeMap hrow
  exact ⟨hspeciesRow, hallocRow, htreeRow⟩

#print axioms zeroth_mark_le_four_mark_max
#print axioms fixed_pointwise_map_transfers_rooted_row
#print axioms fixed_cauchy_cost_transfers_every_rooted_row
#print axioms fixed_support_loss_transfers_rooted_row
#print axioms one_outer_row_pays_fixed_bkar_handoff

end Millennium.YangMills
