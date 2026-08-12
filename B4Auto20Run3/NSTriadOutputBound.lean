import Mathlib

namespace B4Auto20Run3

/-- BANKER: exact incompressible triad cancellation. For `ξ + η = κ`,
orthogonality of the velocity polarization to its own input frequency moves the
nonlinear contraction from the high partner `η` to the output frequency `κ`. -/
theorem ns_triad_output_frequency_identity
    (u ξ η κ : EuclideanSpace ℝ (Fin 3))
    (htriad : ξ + η = κ)
    (hdiv : ⟪u, ξ⟫_ℝ = 0) :
    ⟪u, η⟫_ℝ = ⟪u, κ⟫_ℝ := by
  calc
    ⟪u, η⟫_ℝ = ⟪u, ξ⟫_ℝ + ⟪u, η⟫_ℝ := by rw [hdiv, zero_add]
    _ = ⟪u, ξ + η⟫_ℝ := by rw [inner_add_right]
    _ = ⟪u, κ⟫_ℝ := by rw [htriad]

/-- CLEANER: Cauchy--Schwarz turns the exact cancellation into the quantitative
high-high-to-low suppression bound by the output frequency rather than the high
partner frequency. -/
theorem ns_triad_output_frequency_bound
    (u ξ η κ : EuclideanSpace ℝ (Fin 3))
    (htriad : ξ + η = κ)
    (hdiv : ⟪u, ξ⟫_ℝ = 0) :
    |⟪u, η⟫_ℝ| ≤ ‖u‖ * ‖κ‖ := by
  rw [ns_triad_output_frequency_identity u ξ η κ htriad hdiv]
  exact abs_real_inner_le_norm u κ

/-- CRITIC: the triad relation alone does not give output-frequency suppression.
In the one-dimensional scalar model `ξ=1`, `η=-1`, `κ=0`, a non-divergence-free
polarization has unit interaction with the high partner while the output
frequency is zero. -/
theorem ns_without_divergence_free_cancellation_fails :
    (1 : ℝ) + (-1) = 0 ∧
    |(1 : ℝ) * (-1)| > |(1 : ℝ) * 0| := by
  norm_num

#print axioms B4Auto20Run3.ns_triad_output_frequency_identity
#print axioms B4Auto20Run3.ns_triad_output_frequency_bound
#print axioms B4Auto20Run3.ns_without_divergence_free_cancellation_fails

end B4Auto20Run3
