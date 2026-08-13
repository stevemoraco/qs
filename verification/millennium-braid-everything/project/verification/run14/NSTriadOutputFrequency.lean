import Mathlib

namespace MillenniumRun14

/-- For an exact Fourier triad ξ + η = κ, if the velocity polarization u at ξ
is divergence-free (orthogonal to ξ), then its contraction with the high partner η
is exactly its contraction with the output frequency κ. This is the finite algebraic
core behind the output-frequency bound for high-high-to-low Navier--Stokes triads. -/
theorem ns_triad_output_frequency_identity
    (u ξ η κ : EuclideanSpace ℝ (Fin 3))
    (htriad : ξ + η = κ)
    (hdiv : ⟪u, ξ⟫_ℝ = 0) :
    ⟪u, η⟫_ℝ = ⟪u, κ⟫_ℝ := by
  calc
    ⟪u, η⟫_ℝ = ⟪u, ξ⟫_ℝ + ⟪u, η⟫_ℝ := by rw [hdiv, zero_add]
    _ = ⟪u, ξ + η⟫_ℝ := by rw [inner_add_right]
    _ = ⟪u, κ⟫_ℝ := by rw [htriad]

end MillenniumRun14
