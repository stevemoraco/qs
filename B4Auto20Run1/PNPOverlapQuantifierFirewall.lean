import Mathlib

/-!
B4 AUTO20 run1 — P vs NP overlap-quantifier firewall.

Status at commit: 🟢 PROVED (finite logical core) · 🔵 LEAN-SOURCE · 🟡 compile pending.
Official Millennium status: no P-vs-NP claim.

Exact theorem identities:
* `cofinal_lower_vs_eventual_upper_incompatible`
* `one_lower_witness_can_coexist_with_eventual_upper`

Assumptions: abstract predicates `Lower` and `Upper` on input lengths, pointwise incompatibility,
cofinal recurrence of the lower property, and eventual validity of the upper property.
Provenance: current fixed-exponent/uniformity frontier and B4 AUTO19 pointwise-vs-uniform
quantifier firewall. Official target remains Cook's Clay P-vs-NP problem statement.
Audit: no `sorry`, `admit`, `sorryAx`, custom axiom, `opaque`, or `unsafe` in this source.
Compile status at commit: pending independent runner replay.
Exact remaining gap: prove an unrestricted lower bound with the same model/family/exponent
quantifiers as a collapse theorem. This logic only closes the final overlap once those substantive
complexity hypotheses exist.
-/

namespace B4Auto20Run1.PNP

theorem cofinal_lower_vs_eventual_upper_incompatible
    (Lower Upper : ℕ → Prop)
    (hexcl : ∀ n, Lower n → Upper n → False)
    (hlower : ∀ N, ∃ n, N ≤ n ∧ Lower n)
    (hupper : ∃ N, ∀ n, N ≤ n → Upper n) :
    False := by
  rcases hupper with ⟨N, hN⟩
  rcases hlower N with ⟨n, hn, hL⟩
  exact hexcl n hL (hN n hn)

theorem one_lower_witness_can_coexist_with_eventual_upper :
    let Lower : ℕ → Prop := fun n => n = 0
    let Upper : ℕ → Prop := fun n => 1 ≤ n
    (∀ n, Lower n → Upper n → False) ∧
      (∃ n, Lower n) ∧
      (∃ N, ∀ n, N ≤ n → Upper n) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro n hn hU
    omega
  · exact ⟨0, rfl⟩
  · refine ⟨1, ?_⟩
    intro n hn
    exact hn

#print axioms cofinal_lower_vs_eventual_upper_incompatible
#print axioms one_lower_witness_can_coexist_with_eventual_upper

end B4Auto20Run1.PNP
