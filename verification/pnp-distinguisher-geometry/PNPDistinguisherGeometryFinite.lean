import Mathlib

/-!
# P-vs-NP distinguisher geometry: finite scalar core

This file formalizes only the scalar implications used after the combinatorial
average-sensitivity and monotone-path alternation theorems are supplied.

It does not formalize Boolean cubes, average sensitivity, circuits, `AC⁰`,
Boppana's theorem, PH verification, MCSP, P, NP, or their separation.
-/

namespace MillenniumBraid
namespace PNPDistinguisherGeometryFinite

/-- If scale-`d` output expansion supplies the cross-multiplied sensitivity
budget and every output has sensitivity at most `A`, then `A` must pay the
per-output lower floor. -/
theorem sensitivity_upper_meets_expansion_floor
    (n d m delta total A : ℝ)
    (hd : 0 ≤ d)
    (hm : 0 < m)
    (hLower : delta * m * n ≤ d * total)
    (hUpper : total ≤ m * A) :
    delta * n ≤ d * A := by
  have hchain : delta * m * n ≤ d * (m * A) :=
    hLower.trans (mul_le_mul_of_nonneg_left hUpper hd)
  nlinarith

/-- The path analogue: a total alternation budget bounded by `m*A` cannot meet
`L` coarse blocks of relative cost `delta*m` unless `A ≥ delta*L`. -/
theorem alternation_upper_meets_block_floor
    (L m delta totalAlt A : ℝ)
    (hm : 0 < m)
    (hLower : L * delta * m ≤ totalAlt)
    (hUpper : totalAlt ≤ m * A) :
    L * delta ≤ A := by
  nlinarith

/-- A monotone/antitone output family with at most one transition per output
cannot meet a coarse-path expansion floor above one. -/
theorem monotone_family_path_contradiction
    (L m delta totalAlt : ℝ)
    (hm : 0 < m)
    (hLower : L * delta * m ≤ totalAlt)
    (hMonotone : totalAlt ≤ m)
    (hTooLarge : 1 < L * delta) :
    False := by
  nlinarith

/-- If output `j` is built from `k_j` one-transition tests, the total number of
such tests must pay the complete path-alternation budget. -/
theorem bounded_combination_requires_many_tests
    (L m delta totalAlt totalTests : ℝ)
    (hLower : L * delta * m ≤ totalAlt)
    (hByTests : totalAlt ≤ totalTests) :
    L * delta * m ≤ totalTests := by
  exact hLower.trans hByTests

/-- A union of `r` integer intervals has at most `2r` boundary transitions; the
required average interval count is therefore at least half the path floor. -/
theorem interval_count_floor
    (L m delta totalTransitions totalIntervals : ℝ)
    (hLower : L * delta * m ≤ totalTransitions)
    (hIntervals : totalTransitions ≤ 2 * totalIntervals) :
    (L * delta * m) / 2 ≤ totalIntervals := by
  nlinarith

/-- Combining a source-backed bounded-depth sensitivity upper bound with the
abstract distinguisher lower bound yields the exact scalar size-budget gate. -/
theorem bounded_depth_sensitivity_gate
    (n d delta A : ℝ)
    (hd : 0 < d)
    (hFloor : delta * n ≤ d * A) :
    delta * n / d ≤ A := by
  apply (div_le_iff₀ hd).2
  simpa [mul_comm] using hFloor

/-- Finite exponent bookkeeping behind `n / n^(1-ε) = n^ε`: when `a=b+c`,
`n^a` factors exactly as `n^b n^c`. -/
theorem exponent_budget_identity
    (n : ℝ) (a b c : ℕ)
    (hab : a = b + c) :
    n ^ a = n ^ b * n ^ c := by
  rw [hab, pow_add]

#print axioms sensitivity_upper_meets_expansion_floor
#print axioms alternation_upper_meets_block_floor
#print axioms monotone_family_path_contradiction
#print axioms bounded_combination_requires_many_tests
#print axioms interval_count_floor
#print axioms bounded_depth_sensitivity_gate
#print axioms exponent_budget_identity

end PNPDistinguisherGeometryFinite
end MillenniumBraid
