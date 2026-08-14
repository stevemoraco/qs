import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.UniformSpace.Cauchy

open Filter

namespace Millennium.CrossProblem

/-!
# Unconditional geometric convergence firewall

This file removes "assume the approximation sequence converges" from the
cross-problem proof architecture.

It proves convergence from an explicit quantitative bound on consecutive
increments in a complete metric space. It also proves that any closed native
admissibility class containing all approximants contains the limit.

This is a convergence theorem, not a proof that any particular Millennium
approximation scheme satisfies the required increment bound.
-/

variable {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]

/-- Geometrically decaying consecutive increments force convergence in a
complete metric space. Convergence is a conclusion, not a hypothesis. -/
theorem geometric_steps_tendsto
    (u : ℕ → X) (r C : ℝ)
    (hr : r < 1)
    (hstep : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ C * r ^ n) :
    ∃ x : X, Tendsto u atTop (𝓝 x) := by
  have hcauchy : CauchySeq u :=
    cauchySeq_of_le_geometric r C hr hstep
  exact cauchySeq_tendsto_of_complete hcauchy

/-- Summably controlled consecutive increments force convergence in a complete
metric space. -/
theorem summable_steps_tendsto
    (u : ℕ → X) (d : ℕ → ℝ)
    (hstep : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ d n)
    (hsum : Summable d) :
    ∃ x : X, Tendsto u atTop (𝓝 x) := by
  have hcauchy : CauchySeq u :=
    cauchySeq_of_dist_le_of_summable d hstep hsum
  exact cauchySeq_tendsto_of_complete hcauchy

/-- If every approximant lies in a closed native admissibility class, the
geometric-step limit lies in that class as well. -/
theorem geometric_steps_tendsto_in_closed
    (K : Set X) (hK : IsClosed K)
    (u : ℕ → X) (r C : ℝ)
    (hr : r < 1)
    (hstep : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ C * r ^ n)
    (hmem : ∀ n : ℕ, u n ∈ K) :
    ∃ x : X, x ∈ K ∧ Tendsto u atTop (𝓝 x) := by
  obtain ⟨x, hx⟩ := geometric_steps_tendsto u r C hr hstep
  refine ⟨x, ?_, hx⟩
  exact hK.mem_of_tendsto hx (Eventually.of_forall hmem)

/-- The same closed-limit result for a general summable defect budget. -/
theorem summable_steps_tendsto_in_closed
    (K : Set X) (hK : IsClosed K)
    (u : ℕ → X) (d : ℕ → ℝ)
    (hstep : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ d n)
    (hsum : Summable d)
    (hmem : ∀ n : ℕ, u n ∈ K) :
    ∃ x : X, x ∈ K ∧ Tendsto u atTop (𝓝 x) := by
  obtain ⟨x, hx⟩ := summable_steps_tendsto u d hstep hsum
  refine ⟨x, ?_, hx⟩
  exact hK.mem_of_tendsto hx (Eventually.of_forall hmem)

/-- A uniform closed lower margin also survives the constructed geometric
limit. -/
theorem geometric_real_lower_margin
    (u : ℕ → ℝ) (r C margin : ℝ)
    (hr : r < 1)
    (hstep : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ C * r ^ n)
    (hmargin : ∀ n : ℕ, margin ≤ u n) :
    ∃ x : ℝ, margin ≤ x ∧ Tendsto u atTop (𝓝 x) := by
  obtain ⟨x, hx⟩ := geometric_steps_tendsto u r C hr hstep
  refine ⟨x, ?_, hx⟩
  exact isClosed_Ici.mem_of_tendsto hx (Eventually.of_forall hmargin)

/-- A convenient dyadic specialization. -/
theorem dyadic_steps_tendsto
    (u : ℕ → X) (C : ℝ)
    (hstep : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ C * (1 / 2 : ℝ) ^ n) :
    ∃ x : X, Tendsto u atTop (𝓝 x) := by
  exact geometric_steps_tendsto u (1 / 2 : ℝ) C (by norm_num) hstep

#print axioms geometric_steps_tendsto
#print axioms summable_steps_tendsto
#print axioms geometric_steps_tendsto_in_closed
#print axioms summable_steps_tendsto_in_closed
#print axioms geometric_real_lower_margin
#print axioms dyadic_steps_tendsto

end Millennium.CrossProblem
