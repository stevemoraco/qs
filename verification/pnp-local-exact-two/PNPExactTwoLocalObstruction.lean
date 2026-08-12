import Mathlib

/-!
# P versus NP: local EXACT-2 baseline obstruction

This file formalizes only the finite arithmetic/logical core of an explicit
`2n - 2`-gate `B₂` circuit family described in the accompanying note.  It does
not define Boolean circuits, critical paths, the Chen--Li--Yang magnification
theorem, `P`, `NP`, or `P ≠ NP`.
-/

namespace MillenniumRun16
namespace PNPExactTwoLocal

/-- Weight-level semantics of
`OR(prefix) AND XNOR(XOR(prefix), last)` on total weights at most three.
Here `a` is the number of ones in the prefix and `b` is the last bit. -/
theorem baseline_weight_spec
    (a b : ℕ)
    (hb : b ≤ 1)
    (hsmall : a + b ≤ 3) :
    (0 < a ∧ Even (a + b)) ↔ a + b = 2 := by
  constructor
  · rintro ⟨ha, ⟨q, hq⟩⟩
    omega
  · intro htwo
    constructor
    · omega
    · exact ⟨1, by omega⟩

/-- Fixing a background of weight `w-2` turns exact weight `w` into exact
local weight two.  The lower bound on `w` prevents truncated subtraction. -/
theorem exact_two_after_background
    (w k : ℕ)
    (hw : 2 ≤ w) :
    w - 2 + k = w ↔ k = 2 := by
  omega

/-- Local weights zero through three land exactly in the four adjacent global
layers used by the exact-layer corridor. -/
theorem background_hits_four_adjacent_layers
    (w k : ℕ)
    (hw : 2 ≤ w)
    (hk : k ≤ 3) :
    w - 2 + k = w - 2 ∨
      w - 2 + k = w - 1 ∨
      w - 2 + k = w ∨
      w - 2 + k = w + 1 := by
  omega

/-- Exact promise factorization.  On four adjacent total weights, exact weight
`w` is equivalent to same parity as `w` plus a prefix threshold `a ≥ w-1`.
The existential equality is the division-free parity predicate. -/
theorem four_layer_parity_threshold_factorization
    (w a b : ℤ)
    (hb : b = 0 ∨ b = 1)
    (hpromise :
      a + b = w - 2 ∨
      a + b = w - 1 ∨
      a + b = w ∨
      a + b = w + 1) :
    a + b = w ↔
      ((∃ q : ℤ, a + b - w = 2 * q) ∧ w - 1 ≤ a) := by
  constructor
  · intro hexact
    constructor
    · exact ⟨0, by omega⟩
    · rcases hb with rfl | rfl <;> omega
  · rintro ⟨⟨q, hparity⟩, hthreshold⟩
    rcases hpromise with hlow | hbelow | hexact | habove
    · rcases hb with rfl | rfl <;> omega
    · omega
    · exact hexact
    · omega

/-- The explicit family uses two prefix chains and two final gates. -/
theorem exact_two_baseline_gate_count
    (n : ℕ)
    (hn : 2 ≤ n) :
    (n - 2) + (n - 2) + 2 = 2 * n - 2 := by
  omega

/-- Exact outgoing-wire ledger for the explicit zero-excess topology:
`n-1` prefix inputs have out-degree two, the last input has out-degree one,
and every one of the `2n-3` non-output gates has out-degree one. -/
theorem exact_two_baseline_wire_ledger
    (n : ℕ)
    (hn : 2 ≤ n) :
    2 * (n - 1) + 1 + (2 * n - 3) = 2 * (2 * n - 2) := by
  omega

/-- The single-output branching-excess identity is saturated with output on a
critical path and both excess terms equal to zero. -/
theorem exact_two_baseline_saturates_critical_path_floor
    (n : ℕ)
    (hn : 2 ≤ n) :
    2 * n - 2 = 2 * n - 1 - 1 + 0 + 0 := by
  omega

#print axioms baseline_weight_spec
#print axioms exact_two_after_background
#print axioms background_hits_four_adjacent_layers
#print axioms four_layer_parity_threshold_factorization
#print axioms exact_two_baseline_gate_count
#print axioms exact_two_baseline_wire_ledger
#print axioms exact_two_baseline_saturates_critical_path_floor

end PNPExactTwoLocal
end MillenniumRun16
