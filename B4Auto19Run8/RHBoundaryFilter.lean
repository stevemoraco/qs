import Mathlib

/-!
B4 AUTO19 run8 — RH finite filter/boundary firewall.

Status at commit: 🟢 PROVED (paper algebra) · 🔵 LEAN-SOURCE · 🟡 compile pending.
Official Millennium status: no RH claim.

Exact theorem identities:
* `geometric_two_tap_interior`
* `truncated_first_boundary_value`
* `exact_interior_annihilation_coexists_with_nonzero_boundary`

Assumptions: real scalar `r`, natural index `n`; the final witness specializes to `r = 2`.
Provenance: RH-Lean commits 53420d4a0d259d970a10aca6aa892346f178c92b and
4bc06f4626f073dc64a22bc00e8b77416c6959be (triangular-ray/tent-filter frontier).
Audit: no `sorry`, `admit`, `sorryAx`, custom axiom, `opaque`, or `unsafe` in this source.
Compile status at commit: first hostile replay rejected parser-sensitive spaced absolute-value syntax;
CLEANER replaces it by `abs (...)`; corrected replay pending.
Exact remaining gap: the analytic/arithmetic signed cancellation in the actual Weil/tent formula;
this finite identity only shows that exact interior recurrence cancellation does not control the
first truncation boundary term.
-/

namespace B4Auto19Run8.RH

theorem geometric_two_tap_interior (r : ℝ) (n : ℕ) :
    r ^ (n + 1) - r * r ^ n = 0 := by
  rw [pow_succ]
  ring

theorem truncated_first_boundary_value (r : ℝ) (n : ℕ) :
    0 - r * r ^ n = -(r ^ (n + 1)) := by
  rw [pow_succ]
  ring

theorem exact_interior_annihilation_coexists_with_nonzero_boundary (n : ℕ) :
    ((2 : ℝ) ^ (n + 1) - 2 * (2 : ℝ) ^ n = 0) ∧
    (0 - 2 * (2 : ℝ) ^ n = -((2 : ℝ) ^ (n + 1))) ∧
    0 < abs (-((2 : ℝ) ^ (n + 1))) := by
  constructor
  · exact geometric_two_tap_interior 2 n
  constructor
  · exact truncated_first_boundary_value 2 n
  · rw [abs_neg]
    positivity

#print axioms geometric_two_tap_interior
#print axioms truncated_first_boundary_value
#print axioms exact_interior_annihilation_coexists_with_nonzero_boundary

end B4Auto19Run8.RH
