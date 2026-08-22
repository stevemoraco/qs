import Mathlib

/-!
B4 AUTO19 run8 — BSD one-prime/local-to-global firewall.

Status at commit: 🟢 PROVED (finite logical model) · 🔵 LEAN-SOURCE · 🟡 compile pending.
Official Millennium status: no BSD claim.

Exact theorem identities:
* `same_one_local_coordinate_can_hide_global_defect`
* `all_two_local_coordinates_identify_total_defect`
* `opposite_bounds_force_exactness`

Assumptions: the first two theorems use a two-coordinate nonnegative defect ledger as a
finite model; the third is an abstract natural-number exactification rule.
Provenance: current BSD source-interface correction mirrored in qs PR #150 and the prior
one-prime/omitted-local-term B4 banks.
Audit: no `sorry`, `admit`, `sorryAx`, custom axiom, `opaque`, or `unsafe` in this source.
Compile status at commit: pending independent runner replay.
Exact remaining gap: identify and control every genuine arithmetic contribution in the
BSD leading-term/rank formula; agreement or divisibility at one prime/local coordinate does
not globally exactify the determinant/fundamental-line comparison.
-/

namespace B4Auto19Run8.BSD

def localAtP (s : ℕ × ℕ) : ℕ := s.1

def totalDefect (s : ℕ × ℕ) : ℕ := s.1 + s.2

theorem same_one_local_coordinate_can_hide_global_defect :
    ∃ x y : ℕ × ℕ,
      localAtP x = localAtP y ∧
      totalDefect x ≠ totalDefect y := by
  refine ⟨(1, 0), (1, 1), ?_, ?_⟩
  · rfl
  · norm_num [totalDefect]

theorem all_two_local_coordinates_identify_total_defect
    {x y : ℕ × ℕ}
    (h1 : x.1 = y.1)
    (h2 : x.2 = y.2) :
    totalDefect x = totalDefect y := by
  simp [totalDefect, h1, h2]

theorem opposite_bounds_force_exactness
    {a b : ℕ}
    (hab : a ≤ b)
    (hba : b ≤ a) :
    a = b := by
  exact Nat.le_antisymm hab hba

#print axioms same_one_local_coordinate_can_hide_global_defect
#print axioms all_two_local_coordinates_identify_total_defect
#print axioms opposite_bounds_force_exactness

end B4Auto19Run8.BSD
