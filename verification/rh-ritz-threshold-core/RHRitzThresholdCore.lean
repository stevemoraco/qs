import Mathlib

/-!
# Ritz-threshold stabilization finite core

This file formalizes only the topology/order logic used in
`stevemoraco/RH`'s parity-resolved Ritz-stabilization note.

It does **not** formalize closed quadratic forms, compact resolvents, the
min--max principle, spectral projections, parity reduction, the Weil form,
Xi, zeta, or RH.  Those analytic inputs must instantiate the explicit
sequence hypotheses below.
-/

open Filter Topology

namespace RHRitzThresholdCore

/-- A convergent real sequence eventually lies below any strict upper bound
for its limit. -/
theorem eventually_lt_threshold_of_tendsto
    {u : ℕ → ℝ} {limit threshold : ℝ}
    (hu : Tendsto u atTop (𝓝 limit))
    (h : limit < threshold) :
    ∀ᶠ n in atTop, u n < threshold := by
  exact hu (Iio_mem_nhds h)

/-- A convergent real sequence eventually lies above any strict lower bound
for its limit. -/
theorem eventually_threshold_lt_of_tendsto
    {u : ℕ → ℝ} {limit threshold : ℝ}
    (hu : Tendsto u atTop (𝓝 limit))
    (h : threshold < limit) :
    ∀ᶠ n in atTop, threshold < u n := by
  exact hu (Ioi_mem_nhds h)

/-- Three indexed Ritz sequences inherit a strict exact spectral separation
eventually.  The spectral theorem is external; here the limits and strict
ordering are explicit hypotheses. -/
theorem eventual_parity_threshold_pattern
    {evenGround evenSecond oddGround : ℕ → ℝ}
    {lambdaEvenGround lambdaEvenSecond lambdaOddGround threshold : ℝ}
    (hEvenGround : Tendsto evenGround atTop (𝓝 lambdaEvenGround))
    (hEvenSecond : Tendsto evenSecond atTop (𝓝 lambdaEvenSecond))
    (hOddGround : Tendsto oddGround atTop (𝓝 lambdaOddGround))
    (hBelow : lambdaEvenGround < threshold)
    (hAboveEven : threshold < lambdaEvenSecond)
    (hAboveOdd : threshold < lambdaOddGround) :
    ∀ᶠ n in atTop,
      evenGround n < threshold ∧
      threshold < evenSecond n ∧
      threshold < oddGround n := by
  exact
    (eventually_lt_threshold_of_tendsto hEvenGround hBelow).and
      ((eventually_threshold_lt_of_tendsto hEvenSecond hAboveEven).and
        (eventually_threshold_lt_of_tendsto hOddGround hAboveOdd))

/-- Ritz values are upper bounds for exact eigenvalues.  Hence one certified
finite-band value below a threshold already forces the exact eigenvalue below
that threshold. -/
theorem exact_below_of_ritz_witness
    {exact ritz threshold : ℝ}
    (hUpper : exact ≤ ritz)
    (hWitness : ritz < threshold) :
    exact < threshold :=
  lt_of_le_of_lt hUpper hWitness

/-- An all-band lower barrier survives passage to a sequence limit.  This is
the precise direction unavailable from one finite positive Ritz value. -/
theorem limit_ge_of_all_band_barrier
    {u : ℕ → ℝ} {limit threshold : ℝ}
    (hu : Tendsto u atTop (𝓝 limit))
    (hBarrier : ∀ n, threshold ≤ u n) :
    threshold ≤ limit := by
  by_contra hnot
  have hLimitBelow : limit < threshold := lt_of_not_ge hnot
  have hEventually :=
    eventually_lt_threshold_of_tendsto hu hLimitBelow
  rcases (eventually_atTop.1 hEventually) with ⟨N, hN⟩
  exact (not_lt_of_ge (hBarrier N)) (hN N le_rfl)

/-- If the threshold is known not to equal the exact spectral limit, an
all-band lower barrier becomes a strict exact lower bound. -/
theorem limit_gt_of_all_band_barrier_of_ne
    {u : ℕ → ℝ} {limit threshold : ℝ}
    (hu : Tendsto u atTop (𝓝 limit))
    (hBarrier : ∀ n, threshold ≤ u n)
    (hNotSpectrum : limit ≠ threshold) :
    threshold < limit := by
  have hle : threshold ≤ limit :=
    limit_ge_of_all_band_barrier hu hBarrier
  exact lt_of_le_of_ne hle (Ne.symm hNotSpectrum)

/-- A uniform positive finite-band margin gives a strict exact lower bound
without a separate non-spectrum hypothesis. -/
theorem limit_gt_of_uniform_margin
    {u : ℕ → ℝ} {limit threshold margin : ℝ}
    (hu : Tendsto u atTop (𝓝 limit))
    (hMargin : 0 < margin)
    (hBarrier : ∀ n, threshold + margin ≤ u n) :
    threshold < limit := by
  have hle : threshold + margin ≤ limit :=
    limit_ge_of_all_band_barrier hu hBarrier
  linarith

/-- Combining one finite witness with two uniform barriers yields the exact
strict parity-threshold ordering once convergence hypotheses are supplied. -/
theorem exact_parity_pattern_of_witness_and_uniform_barriers
    {evenGroundRitz : ℝ}
    {evenSecond oddGround : ℕ → ℝ}
    {lambdaEvenGround lambdaEvenSecond lambdaOddGround threshold margin : ℝ}
    (hGroundUpper : lambdaEvenGround ≤ evenGroundRitz)
    (hGroundWitness : evenGroundRitz < threshold)
    (hEvenSecond : Tendsto evenSecond atTop (𝓝 lambdaEvenSecond))
    (hOddGround : Tendsto oddGround atTop (𝓝 lambdaOddGround))
    (hMargin : 0 < margin)
    (hEvenBarrier : ∀ n, threshold + margin ≤ evenSecond n)
    (hOddBarrier : ∀ n, threshold + margin ≤ oddGround n) :
    lambdaEvenGround < threshold ∧
      threshold < lambdaEvenSecond ∧
      threshold < lambdaOddGround := by
  exact ⟨
    exact_below_of_ritz_witness hGroundUpper hGroundWitness,
    limit_gt_of_uniform_margin hEvenSecond hMargin hEvenBarrier,
    limit_gt_of_uniform_margin hOddGround hMargin hOddBarrier
  ⟩

#print axioms eventually_lt_threshold_of_tendsto
#print axioms eventually_threshold_lt_of_tendsto
#print axioms eventual_parity_threshold_pattern
#print axioms exact_below_of_ritz_witness
#print axioms limit_ge_of_all_band_barrier
#print axioms limit_gt_of_all_band_barrier_of_ne
#print axioms limit_gt_of_uniform_margin
#print axioms exact_parity_pattern_of_witness_and_uniform_barriers

end RHRitzThresholdCore
