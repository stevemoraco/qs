import Mathlib

/-!
Finite algebraic core for the exact Navier–Stokes spectral-flux audit.

The analytic/Fourier theorem exhibiting a nonzero crossing triad is proved in
`research/navier_stokes/NS_HELICAL_FLUX_SCALING_COUNTEREXAMPLE_2026-08-12.md`.
This file formalizes only the two load-bearing scalar contradictions:

* a cubic quantity cannot have one global quadratic ceiling over all amplitudes;
* a linearly growing quantity cannot have one global inverse-scale ceiling.

These are helper/obstruction theorems, not the Clay Navier–Stokes statement.
-/

namespace NSFluxScalingObstruction

/-- For every nonnegative proposed quadratic coefficient `D`, a positive
amplitude exists for which the cubic model `amp^3/4` exceeds `D * amp^2`. -/
theorem cubic_beats_quadratic (D : ℝ) (hD : 0 ≤ D) :
    ∃ amp : ℝ, 0 < amp ∧ D * amp ^ 2 < amp ^ 3 / 4 := by
  let amp : ℝ := 4 * D + 1
  have hamp : 0 < amp := by
    dsimp [amp]
    linarith
  refine ⟨amp, hamp, ?_⟩
  have hbase : D < amp / 4 := by
    dsimp [amp]
    linarith
  have hsq : 0 < amp ^ 2 := by positivity
  calc
    D * amp ^ 2 < (amp / 4) * amp ^ 2 := mul_lt_mul_of_pos_right hbase hsq
    _ = amp ^ 3 / 4 := by ring

/-- There is no finite nonnegative coefficient that bounds the cubic model by
a quadratic model at every positive amplitude. -/
theorem no_global_cubic_by_quadratic_ceiling :
    ¬ ∃ D : ℝ, 0 ≤ D ∧ ∀ amp : ℝ, 0 < amp → amp ^ 3 / 4 ≤ D * amp ^ 2 := by
  rintro ⟨D, hD, hceiling⟩
  obtain ⟨amp, hamp, hstrict⟩ := cubic_beats_quadratic D hD
  exact (not_lt_of_ge (hceiling amp hamp)) hstrict

/-- For every nonnegative proposed inverse-scale coefficient `D`, a positive
scale exists for which the linear model `s/4` exceeds `D/s`. -/
theorem linear_beats_inverse (D : ℝ) (hD : 0 ≤ D) :
    ∃ s : ℝ, 0 < s ∧ D / s < s / 4 := by
  let s : ℝ := 4 * D + 1
  have hs : 0 < s := by
    dsimp [s]
    linarith
  refine ⟨s, hs, ?_⟩
  rw [div_lt_iff₀ hs]
  dsimp [s]
  nlinarith [sq_nonneg D]

/-- There is no finite nonnegative coefficient that bounds the linear model by
an inverse-scale model at every positive scale. -/
theorem no_global_linear_by_inverse_ceiling :
    ¬ ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℝ, 0 < s → s / 4 ≤ D / s := by
  rintro ⟨D, hD, hceiling⟩
  obtain ⟨s, hs, hstrict⟩ := linear_beats_inverse D hD
  exact (not_lt_of_ge (hceiling s hs)) hstrict

#print axioms NSFluxScalingObstruction.cubic_beats_quadratic
#print axioms NSFluxScalingObstruction.no_global_cubic_by_quadratic_ceiling
#print axioms NSFluxScalingObstruction.linear_beats_inverse
#print axioms NSFluxScalingObstruction.no_global_linear_by_inverse_ceiling

end NSFluxScalingObstruction
