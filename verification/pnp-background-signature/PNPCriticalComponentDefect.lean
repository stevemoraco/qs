import Mathlib

/-!
# P versus NP: critical-component defect conservation finite core

HONESTY BOUNDARY

This file formalizes only integer wire-ledger cancellation and the scalar
component-error inequality used in round 203. It does not formalize circuit
syntax, critical paths, graph components, Chen--Li--Yang Lemma 4.8, hardness
magnification, `P`, `NP`, or `P != NP`.
-/

namespace MillenniumRun203
namespace PNPCriticalComponentDefect

/-- Cancellation of the internal `T₁ -> T₁` wire count in the two-class
wire ledger. The hypotheses are the exact outgoing/incoming equations supplied
by the graph decomposition. -/
theorem critical_component_vertex_identity
    (c1 c2 n K m o e1 e2 ell E12 E22 : ℤ)
    (h12 : E12 = c1 + K - 2 * o + e1 - ell)
    (h22 : E22 = c2 - m + o + e2 - 2 * (c1 - n) + ell)
    (hin2 : 2 * c2 = E12 + E22) :
    c1 + c2 = 2 * n + K - m - o + e1 + e2 := by
  linarith

/-- Gate-count form of the critical-component identity. -/
theorem critical_component_gate_identity
    (c1 c2 n K m o e1 e2 ell E12 E22 g : ℤ)
    (h12 : E12 = c1 + K - 2 * o + e1 - ell)
    (h22 : E22 = c2 - m + o + e2 - 2 * (c1 - n) + ell)
    (hin2 : 2 * c2 = E12 + E22)
    (hgates : g = (c1 - n) + c2) :
    g = n + K - m - o + e1 + e2 := by
  have hvertices :=
    critical_component_vertex_identity
      c1 c2 n K m o e1 e2 ell E12 E22 h12 h22 hin2
  linarith

/-- In the single-output case, additive gate surplus equals branching excess
minus the path-merger deficit, plus the output-location correction. -/
theorem single_output_defect_conservation
    (g n K o e : ℤ)
    (hgate : g = n + K - 1 - o + e) :
    g - (2 * n - 2) = e - (n - K) + (1 - o) := by
  linarith

/-- The doubled pair-count inequality implies that one component contributes
at least `r-1` vertex/pair errors. Here `r=t+k`, where `t` is the number of
vertex errors and `k` is the number of remaining vertices; `2*p >= k(k-1)` is
the division-free form of `p >= binom(k,2)`. -/
theorem component_error_lower_bound
    (r t k p : ℤ)
    (hr : r = t + k)
    (ht : 0 ≤ t)
    (hk : 0 ≤ k)
    (hp : k * (k - 1) ≤ 2 * p) :
    r - 1 ≤ t + p := by
  by_cases hk_small : k ≤ 1
  · have hp_nonneg : 0 ≤ p := by nlinarith [hp]
    rw [hr]
    nlinarith
  · have hk_two : 2 ≤ k := by omega
    have hprod : 0 ≤ (k - 1) * (k - 2) := by
      exact mul_nonneg (by omega) (by omega)
    rw [hr]
    nlinarith [hp, hprod]

/-- Sum of the componentwise error lower bounds over a finite component
family. -/
theorem sum_component_error_lower_bound
    {J : Type*}
    [Fintype J]
    (r t k p : J → ℤ)
    (hr : ∀ j, r j = t j + k j)
    (ht : ∀ j, 0 ≤ t j)
    (hk : ∀ j, 0 ≤ k j)
    (hp : ∀ j, k j * (k j - 1) ≤ 2 * p j) :
    (∑ j, (r j - 1)) ≤ ∑ j, (t j + p j) := by
  exact Finset.sum_le_sum fun j _ =>
    component_error_lower_bound
      (r j) (t j) (k j) (p j) (hr j) (ht j) (hk j) (hp j)

#print axioms critical_component_vertex_identity
#print axioms critical_component_gate_identity
#print axioms single_output_defect_conservation
#print axioms component_error_lower_bound
#print axioms sum_component_error_lower_bound

end PNPCriticalComponentDefect
end MillenniumRun203
