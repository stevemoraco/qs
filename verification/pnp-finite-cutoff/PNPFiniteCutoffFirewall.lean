import Mathlib

/-!
# P versus NP: finite-cutoff firewall

This file proves a deliberately abstract obstruction.  Any finite table of
apparent lower bounds can be matched by a sequence which becomes identically
zero immediately after the checked range.  Therefore a finite computation does
not, by itself, imply an asymptotic circuit lower bound.

This is not a formalization of Boolean circuits, P, NP, or `P != NP`.
-/

namespace Millennium
namespace PNPFiniteCutoff

/-- A sequence that looks larger than `n^k` through cutoff `N`, then vanishes. -/
def deceptiveComplexity (N k n : ℕ) : ℕ :=
  if n ≤ N then n ^ k + 1 else 0

theorem beats_degree_through_cutoff
    (N k n : ℕ) (hn : n ≤ N) :
    n ^ k < deceptiveComplexity N k n := by
  simp [deceptiveComplexity, hn]

theorem vanishes_after_cutoff
    (N k n : ℕ) (hn : N < n) :
    deceptiveComplexity N k n = 0 := by
  simp [deceptiveComplexity, Nat.not_le.mpr hn]

/-- The same sequence is eventually bounded by the constant zero. -/
theorem eventually_constant_zero (N k : ℕ) :
    ∀ n : ℕ, N + 1 ≤ n → deceptiveComplexity N k n ≤ 0 := by
  intro n hn
  have hNn : N < n := by omega
  simp [vanishes_after_cutoff N k n hNn]

/-- Exact countermodel to the finite-to-asymptotic inference. -/
theorem finite_lower_bound_does_not_force_asymptotic_growth
    (N k : ℕ) :
    ∃ C : ℕ → ℕ,
      (∀ n ≤ N, n ^ k < C n) ∧
      (∀ n, N + 1 ≤ n → C n ≤ 0) := by
  refine ⟨deceptiveComplexity N k, ?_, eventually_constant_zero N k⟩
  intro n hn
  exact beats_degree_through_cutoff N k n hn

#print axioms beats_degree_through_cutoff
#print axioms vanishes_after_cutoff
#print axioms eventually_constant_zero
#print axioms finite_lower_bound_does_not_force_asymptotic_growth

end PNPFiniteCutoff
end Millennium
