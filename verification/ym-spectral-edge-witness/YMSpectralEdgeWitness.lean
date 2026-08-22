import Mathlib

/-!
# Yang--Mills spectral-edge witness finite core

Honesty status: finite real algebra and logarithm bookkeeping only. This file
does not formalize Hilbert-space spectral theory, lattice gauge theory,
Osterwalder--Schrader reconstruction, a continuum quantum field theory, or any
official Millennium statement.
-/

namespace MillenniumBraid
namespace YMSpectralEdgeWitness

/-- A visible near-edge witness with relative Rayleigh defect transfers a scalar
spectral lower bound. This is finite real algebra only. -/
theorem visibility_normalized_witness
    (lam target s r z θ : ℝ)
    (hs : 0 < s)
    (htarget : 0 ≤ target)
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hupper : z ≤ lam * s)
    (hlower : target * s - r ≤ z)
    (hrel : r ≤ θ * target * s) :
    (1 - θ) * target ≤ lam := by
  have hmul : ((1 - θ) * target) * s ≤ lam * s := by
    nlinarith
  by_contra hnot
  have hlt : lam < (1 - θ) * target := lt_of_not_ge hnot
  have hstrict : lam * s < ((1 - θ) * target) * s :=
    mul_lt_mul_of_pos_right hlt hs
  exact (not_lt_of_ge hmul) hstrict

/-- Arbitrarily small absolute defects do not imply a positive transferred
spectral bound when visibility shrinks at the same rate. -/
theorem small_absolute_defect_can_hide_zero_visibility
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s r z lam target : ℝ,
      0 < s ∧ 0 < r ∧ r < ε ∧
      target = 1 ∧ lam = 0 ∧
      z ≤ lam * s ∧ target * s - r ≤ z ∧ lam < target := by
  refine ⟨ε / 2, ε / 2, 0, 0, 1, ?_⟩
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · norm_num
  constructor
  · ring_nf
    norm_num
  · norm_num

/-- The exact logarithmic loss corresponding to a multiplicative transfer
factor `exp (-η) * (1 - θ)`. -/
theorem effective_defect_factor
    (η θ : ℝ)
    (hθ : θ < 1) :
    Real.exp (-(η - Real.log (1 - θ))) =
      Real.exp (-η) * (1 - θ) := by
  have hpos : 0 < 1 - θ := by linarith
  have harg : -(η - Real.log (1 - θ)) =
      -η + Real.log (1 - θ) := by ring
  rw [harg, Real.exp_add, Real.exp_log hpos]

/-- Algebraic conversion of a dimensionless reverse transfer loss into
physical gap units when `a_coarse = b * a_fine`. -/
theorem reverse_physical_gap_step
    (δfine δcoarse ξ afine acoarse b : ℝ)
    (hafine : 0 < afine)
    (hb : 0 < b)
    (hscale : acoarse = b * afine)
    (hgap : δcoarse ≤ b * δfine + ξ) :
    δcoarse / acoarse - ξ / acoarse ≤ δfine / afine := by
  have hacoarse : 0 < acoarse := by
    rw [hscale]
    exact mul_pos hb hafine
  rw [← sub_div]
  apply (div_le_iff₀ hacoarse).2
  have hrhs : (δfine / afine) * acoarse = b * δfine := by
    rw [hscale]
    field_simp [ne_of_gt hafine]
  rw [hrhs]
  linarith

#print axioms visibility_normalized_witness
#print axioms small_absolute_defect_can_hide_zero_visibility
#print axioms effective_defect_factor
#print axioms reverse_physical_gap_step

end YMSpectralEdgeWitness
end MillenniumBraid
