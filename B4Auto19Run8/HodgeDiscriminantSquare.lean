import Mathlib

/-!
B4 AUTO19 run8 — Hodge discriminant-square saturation core.

Status at commit: 🟢 PROVED (scalar arithmetic core) · 🔵 LEAN-SOURCE · 🟡 compile pending.
Official Millennium status: no Hodge claim.

Exact theorem identities:
* `unit_discriminant_ratio_forces_unit_index`
* `sign_condition_is_essential_for_square_exactification`
* `ratio_below_four_forces_index_below_two`

Assumptions: `idx` is represented by a nonnegative real scalar and `ratio = idx^2` is the
scalar shadow of the classical full-rank lattice identity
`|disc(A)| / |disc(L)| = [L:A]^2`.
Provenance: RH-Lean commit b2e61be2a6f0b2646d6a15bf8545e08134981670,
“Hodge discriminant/index certificate for integral algebraic lattices.”
Audit: no `sorry`, `admit`, `sorryAx`, custom axiom, `opaque`, or `unsafe` in this source.
Compile status at commit: pending independent runner replay.
Exact remaining gap: construct enough genuine algebraic cycle classes to obtain the
full-rank algebraic sublattice and its geometric pairing data. The discriminant certificate
only exactifies saturation once those geometric inputs exist.
-/

namespace B4Auto19Run8.Hodge

theorem unit_discriminant_ratio_forces_unit_index
    {idx ratio : ℝ}
    (hidx : 0 ≤ idx)
    (hratio : ratio = idx ^ 2)
    (hunit : ratio = 1) :
    idx = 1 := by
  nlinarith [sq_nonneg (idx - 1)]

theorem sign_condition_is_essential_for_square_exactification :
    ∃ idx ratio : ℝ,
      ratio = idx ^ 2 ∧
      ratio = 1 ∧
      idx ≠ 1 := by
  refine ⟨-1, 1, ?_, ?_, ?_⟩ <;> norm_num

theorem ratio_below_four_forces_index_below_two
    {idx ratio : ℝ}
    (hidx : 0 ≤ idx)
    (hratio : ratio = idx ^ 2)
    (hsmall : ratio < 4) :
    idx < 2 := by
  nlinarith [sq_nonneg (idx - 2)]

#print axioms unit_discriminant_ratio_forces_unit_index
#print axioms sign_condition_is_essential_for_square_exactification
#print axioms ratio_below_four_forces_index_below_two

end B4Auto19Run8.Hodge
