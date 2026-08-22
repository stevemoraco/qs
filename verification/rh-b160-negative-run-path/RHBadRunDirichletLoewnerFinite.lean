import Mathlib

/-!
# RH B160A bad-run Dirichlet-Loewner finite core

Finite scalar inequalities only.

The human B160A reduction uses the standard Dirichlet path Laplacian on the
subspace supported by sampled negative runs.  A bad component of length at most
`R` satisfies a Poincare estimate `normSq <= R^2 * energy`; conversely a long
bad component has an explicit triangular test vector with `energy <= R+1` and
`normSq >= R^3/64`.  The declarations below formalize only the final scalar
consequences of those finite estimates.

They do not formalize the path Laplacian, matrix Loewner order, matrix inertia,
Bhattacharya--Martin--Simpson, Landau's theorem, primes, zeta zeros, BGST, B46,
or RH.
-/

namespace RHBadRunDirichletLoewnerFinite

/-- Rearrangement of the componentwise Poincare estimate. -/
theorem poincare_lower_energy
    {R normSq energy : ℝ}
    (hR : 0 < R)
    (hPoincare : normSq ≤ R ^ 2 * energy) :
    normSq / R ^ 2 ≤ energy := by
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  exact (div_le_iff₀ hR2).2 hPoincare

/-- Crude triangular-witness composition.  If a run of length `R >= 1` has a
witness with `energy <= R+1` and `normSq >= R^3/64`, then its Rayleigh quotient
obeys the cross-multiplied bound `energy * R^2 <= 128 * normSq`. -/
theorem triangular_witness_cross_bound
    {R normSq energy : ℝ}
    (hR : 1 ≤ R)
    (hEnergy : energy ≤ R + 1)
    (hNorm : R ^ 3 / 64 ≤ normSq) :
    energy * R ^ 2 ≤ 128 * normSq := by
  have hR0 : 0 ≤ R := by linarith
  have h1 : energy * R ^ 2 ≤ (R + 1) * R ^ 2 :=
    mul_le_mul_of_nonneg_right hEnergy (sq_nonneg R)
  have h2 : (R + 1) * R ^ 2 ≤ 2 * R ^ 3 := by
    nlinarith [sq_nonneg R]
  have h3 : 2 * R ^ 3 ≤ 128 * normSq := by
    nlinarith [hNorm]
  exact h1.trans (h2.trans h3)

/-- A positive power run exponent beats every strictly smaller subpower exponent
at the exponent-bookkeeping level. -/
theorem power_run_beats_subpower_exponent
    {delta eps : ℝ} (hdelta : 0 < delta) (heps : eps < 2 * delta) :
    -2 * delta < -eps := by
  linarith

/-- The coercivity exponent corresponding to an allowed bad-run exponent `eta`
is exactly twice `eta`. -/
theorem run_to_coercivity_exponent (eta : ℝ) :
    2 * eta = eta + eta := by
  ring

/-- Combining sampler-gap exponent `sigma` and allowed run exponent `eta`
recovers the B160 half-strip width. -/
theorem coercivity_strip_identity (sigma eta : ℝ) :
    (sigma + eta) / 2 = sigma / 2 + eta / 2 := by
  ring

#print axioms poincare_lower_energy
#print axioms triangular_witness_cross_bound
#print axioms power_run_beats_subpower_exponent
#print axioms run_to_coercivity_exponent
#print axioms coercivity_strip_identity

end RHBadRunDirichletLoewnerFinite
