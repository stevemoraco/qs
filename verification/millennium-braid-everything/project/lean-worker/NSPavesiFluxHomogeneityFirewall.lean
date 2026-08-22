import Mathlib

namespace NSPavesiFluxHomogeneityFirewall

/-!
# Cubic-flux versus quadratic-energy homogeneity firewall

The standard Navier--Stokes spectral energy flux is cubic under amplitude
scaling, while a product `sqrt(E_tail) * sqrt(E_total)` is quadratic.  This
pure real-algebra file proves that any nonzero cubic witness eventually exceeds
every fixed quadratic coefficient.

The analytic identification of a particular Fourier triad and its exact flux is
banked separately.  This file does not prove or disprove Navier--Stokes.
-/

/-- A positive cubic coefficient eventually beats any nonnegative quadratic
coefficient. -/
theorem exists_scale_cubic_beats_quadratic
    (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B) :
    ∃ lambda : ℝ,
      0 < lambda ∧ B * lambda ^ 2 < A * lambda ^ 3 := by
  let lambda : ℝ := B / A + 1
  have hAne : A ≠ 0 := ne_of_gt hA
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    have hdiv : 0 ≤ B / A := div_nonneg hB (le_of_lt hA)
    linarith
  have hscale : A * lambda = B + A := by
    dsimp [lambda]
    field_simp [hAne]
    ring
  have hBlt : B < A * lambda := by
    rw [hscale]
    linarith
  have hlambdaSq : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
  have hmul := mul_lt_mul_of_pos_right hBlt hlambdaSq
  refine ⟨lambda, hlambda, ?_⟩
  nlinarith [hmul]

/-- There is no universal quadratic upper bound for a positive cubic response. -/
theorem no_universal_quadratic_bound_for_positive_cubic
    (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B) :
    ¬ (∀ lambda : ℝ,
        0 < lambda → A * lambda ^ 3 ≤ B * lambda ^ 2) := by
  intro hbound
  obtain ⟨lambda, hlambda, hbreak⟩ :=
    exists_scale_cubic_beats_quadratic A B hA hB
  exact (not_lt_of_ge (hbound lambda hlambda)) hbreak

/-- Abstract scaling form.  If `flux(lambda)=lambda^3 flux(1)` and the proposed
right side is `lambda^2 B`, a universal estimate forces the base flux to vanish.
The theorem is stated contrapositively for direct use as a firewall. -/
theorem nonzero_cubic_witness_refutes_absolute_quadratic_bound
    (baseFlux B : ℝ)
    (hFlux : 0 < baseFlux)
    (hB : 0 ≤ B) :
    ∃ lambda : ℝ,
      0 < lambda ∧
      B * lambda ^ 2 < baseFlux * lambda ^ 3 := by
  exact exists_scale_cubic_beats_quadratic baseFlux B hFlux hB

/-- The exact normalized triad in the companion audit has base flux `2`. -/
theorem exact_flux_two_breaks_every_quadratic_coefficient
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ lambda : ℝ,
      0 < lambda ∧ B * lambda ^ 2 < 2 * lambda ^ 3 := by
  exact exists_scale_cubic_beats_quadratic 2 B (by norm_num) hB

#print axioms exists_scale_cubic_beats_quadratic
#print axioms no_universal_quadratic_bound_for_positive_cubic
#print axioms nonzero_cubic_witness_refutes_absolute_quadratic_bound
#print axioms exact_flux_two_breaks_every_quadratic_coefficient

end NSPavesiFluxHomogeneityFirewall
