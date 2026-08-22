import Mathlib

/-!
# Intermediate-root conditioning firewall

Finite real algebra only.

A uniform estimate for a fully composed endpoint response does not, by itself,
control the norm of an intermediate retained root.  Large amplification can be
hidden by a later reciprocal contraction.  The positive repair is an
independent observability estimate in the intermediate norm.

This file does not formalize the Kirk manuscript, replica--BKAR, a polymer
expansion, Osterwalder--Schrader reconstruction, Yang--Mills theory, or a mass
gap.
-/

namespace YMIntermediateRootConditioningFirewall

/-- A scale-dependent upstream map with arbitrarily large intermediate gain. -/
def upstream (M x : ℝ) : ℝ := M * x

/-- A downstream map that exactly cancels the upstream gain when `M ≠ 0`. -/
noncomputable def downstream (M y : ℝ) : ℝ := y / M

/-- The fully composed endpoint map is the identity even though the
intermediate map may be arbitrarily large. -/
theorem endpoint_composition_identity (M x : ℝ) (hM : M ≠ 0) :
    downstream M (upstream M x) = x := by
  unfold downstream upstream
  field_simp [hM]

/-- At the unit input, the endpoint response stays exactly one while the
intermediate response exceeds any prescribed real threshold. -/
theorem arbitrary_intermediate_amplification (K : ℝ) :
    ∃ M : ℝ,
      0 < M ∧
      downstream M (upstream M 1) = 1 ∧
      K < |upstream M 1| := by
  let M : ℝ := K ^ 2 + 1
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hKM : K < M := by
    dsimp [M]
    nlinarith [sq_nonneg (K - (1 / 2 : ℝ))]
  refine ⟨M, hMpos, ?_, ?_⟩
  · exact endpoint_composition_identity M 1 (ne_of_gt hMpos)
  · simpa [upstream, abs_of_pos hMpos] using hKM

/-- There is no single scalar bound that can be inferred simultaneously for
all intermediate responses from this uniformly bounded endpoint family. -/
theorem no_uniform_intermediate_bound_from_endpoint_family :
    ¬ ∃ C : ℝ, ∀ M : ℝ, 0 < M →
      |downstream M (upstream M 1)| ≤ C ∧
      |upstream M 1| ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨M, hMpos, _, hlarge⟩ := arbitrary_intermediate_amplification C
  have hintermediate := (hC M hMpos).2
  exact (not_lt_of_ge hintermediate) hlarge

/-- A lower observability estimate for the downstream map repairs the failed
endpoint-to-intermediate inference.  The conclusion is kept in the
multiplicative currency actually needed in rooted norm comparisons. -/
theorem endpoint_plus_observability_controls_intermediate
    (c K a b x : ℝ)
    (hobserve : c * |a * x| ≤ |b * (a * x)|)
    (hendpoint : |b * (a * x)| ≤ K * |x|) :
    c * |a * x| ≤ K * |x| := by
  exact hobserve.trans hendpoint

/-- If the observability constant is positive, the same repair can be written
as an explicit bound on the intermediate response. -/
theorem endpoint_plus_positive_observability_controls_intermediate
    (c K a b x : ℝ)
    (hc : 0 < c)
    (hobserve : c * |a * x| ≤ |b * (a * x)|)
    (hendpoint : |b * (a * x)| ≤ K * |x|) :
    |a * x| ≤ (K * |x|) / c := by
  apply (le_div_iff₀ hc).2
  calc
    |a * x| * c = c * |a * x| := mul_comm _ _
    _ ≤ K * |x| := hobserve.trans hendpoint

#print axioms endpoint_composition_identity
#print axioms arbitrary_intermediate_amplification
#print axioms no_uniform_intermediate_bound_from_endpoint_family
#print axioms endpoint_plus_observability_controls_intermediate
#print axioms endpoint_plus_positive_observability_controls_intermediate

end YMIntermediateRootConditioningFirewall
