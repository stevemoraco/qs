import Mathlib

/-!
B4 AUTO20 run1 — RH signed-error margin firewall.

Status at commit: 🟢 PROVED (finite scalar core) · 🔵 LEAN-SOURCE · 🟡 compile pending.
Official Millennium status: no Riemann Hypothesis claim.

Exact theorem identities:
* `nonnegative_sign_survives_closed_error_budget`
* `strict_sign_survives_strict_error_budget`
* `oversized_error_budget_can_flip_sign`

Assumptions: real scalar main term, additive error, and explicit sign margin `δ`.
Provenance: current triangular/tent Weil-sign frontier and B4 AUTO19 boundary-filter
obstruction. Official target remains the Clay/Bombieri RH statement.
Audit: no `sorry`, `admit`, `sorryAx`, custom axiom, `opaque`, or `unsafe` in this source.
Compile status at commit: pending independent runner replay.
Exact remaining gap: prove a genuine arithmetic/polar error estimate for the actual Weil/tent
functional whose bound fits inside the available sign margin. The scalar lemma supplies no such
estimate and is not an RH theorem.
-/

namespace B4Auto20Run1.RH

/-- BANKER/CLEANER: a candidate nonnegative main term remains nonnegative after an
additive error when the full absolute error budget fits inside the certified margin. -/
theorem nonnegative_sign_survives_closed_error_budget
    (main err δ : ℝ)
    (hmain : δ ≤ main)
    (herr : |err| ≤ δ) :
    0 ≤ main + err := by
  have hlow : -δ ≤ err := (abs_le.mp herr).1
  linarith

/-- Strict version: strict control of the error against the same margin preserves strict
positivity. -/
theorem strict_sign_survives_strict_error_budget
    (main err δ : ℝ)
    (hmain : δ ≤ main)
    (herr : |err| < δ) :
    0 < main + err := by
  have hlow : -δ < err := (abs_lt.mp herr).1
  linarith

/-- CRITIC: if the allowed absolute error is larger than the available margin, the sign can
flip even with a positive certified main term. -/
theorem oversized_error_budget_can_flip_sign :
    ∃ main err δ : ℝ,
      0 < δ ∧
      δ ≤ main ∧
      |err| ≤ 2 * δ ∧
      main + err < 0 := by
  refine ⟨1, -2, 1, ?_, ?_, ?_, ?_⟩ <;> norm_num

#print axioms nonnegative_sign_survives_closed_error_budget
#print axioms strict_sign_survives_strict_error_budget
#print axioms oversized_error_budget_can_flip_sign

end B4Auto20Run1.RH
