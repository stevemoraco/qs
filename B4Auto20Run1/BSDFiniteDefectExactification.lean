import Mathlib

/-!
B4 AUTO20 run1 — BSD finite local-defect exactification firewall.

Status at commit: 🟢 PROVED (finite scalar core) · 🔵 LEAN-SOURCE · 🟡 compile pending.
Official Millennium status: no Birch–Swinnerton-Dyer claim.

Exact theorem identities:
* `finite_nonnegative_defect_ledger_exact`
* `nonnegative_ledger_total_nonpositive_forces_exact`
* `one_vanishing_defect_can_hide_positive_total`

Assumptions: a finite family of real-valued defect terms, each nonnegative.
Provenance: current BSD local/global leading-term ledger and B4 AUTO19 one-coordinate
obstruction. Official target remains Wiles's Clay BSD problem description.
Audit: no `sorry`, `admit`, `sorryAx`, custom axiom, `opaque`, or `unsafe` in this source.
Compile status at commit: pending independent runner replay.
Exact remaining gap: identify the actual BSD global defect with a finite/nonnegative ledger (or
otherwise prove the needed opposite inequality) including every local and global arithmetic
factor. This finite lemma supplies none of those arithmetic hypotheses.
-/

namespace B4Auto20Run1.BSD

theorem finite_nonnegative_defect_ledger_exact
    {ι : Type*} [Fintype ι]
    (d : ι → ℝ)
    (hnonneg : ∀ i, 0 ≤ d i) :
    (∑ i, d i = 0) ↔ ∀ i, d i = 0 := by
  exact Fintype.sum_eq_zero_iff_of_nonneg hnonneg

theorem nonnegative_ledger_total_nonpositive_forces_exact
    {ι : Type*} [Fintype ι]
    (d : ι → ℝ)
    (hnonneg : ∀ i, 0 ≤ d i)
    (htotal : (∑ i, d i) ≤ 0) :
    ∀ i, d i = 0 := by
  have hsum_nonneg : 0 ≤ ∑ i, d i := Fintype.sum_nonneg hnonneg
  have hzero : (∑ i, d i) = 0 := le_antisymm htotal hsum_nonneg
  exact (finite_nonnegative_defect_ledger_exact d hnonneg).mp hzero

theorem one_vanishing_defect_can_hide_positive_total :
    ∃ d₁ d₂ : ℝ,
      0 ≤ d₁ ∧
      0 ≤ d₂ ∧
      d₁ = 0 ∧
      0 < d₁ + d₂ := by
  refine ⟨0, 1, ?_, ?_, ?_, ?_⟩ <;> norm_num

#print axioms finite_nonnegative_defect_ledger_exact
#print axioms nonnegative_ledger_total_nonpositive_forces_exact
#print axioms one_vanishing_defect_can_hide_positive_total

end B4Auto20Run1.BSD
