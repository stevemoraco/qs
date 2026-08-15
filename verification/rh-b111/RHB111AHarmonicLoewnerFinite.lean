import Mathlib

/-!
# RH B111A harmonic Loewner floor finite scalar core

Finite real/order algebra only.

The matrix theorem in B111A reduces, after diagonalization/order of the negative
spectrum, to the scalar equivalence formalized here: a weak rank-depth bound
`r*x <= C` is exactly the positivity of the corresponding harmonic-shifted
scalar `-x + C/r`.

This file does NOT formalize Hermitian spectral theory, unitary diagonalization,
primes, zeta, or RH.
-/

namespace RHB111AHarmonicLoewnerFinite

/-- A harmonic scalar floor is exactly a weak rank-depth bound. -/
theorem harmonic_floor_scalar_iff
    {x C r : ℝ} (hr : 0 < r) :
    0 ≤ -x + C / r ↔ r * x ≤ C := by
  constructor
  · intro h
    have hdiv : x ≤ C / r := by linarith
    exact (le_div_iff₀ hr).mp hdiv
  · intro h
    have hdiv : x ≤ C / r := (le_div_iff₀ hr).2 h
    linarith

/-- If a rank-depth bound holds with budget `C`, then any larger nonnegative
budget also supplies the harmonic floor. -/
theorem harmonic_floor_mono
    {x C D r : ℝ} (hr : 0 < r)
    (hCD : C ≤ D)
    (hweak : r * x ≤ C) :
    0 ≤ -x + D / r := by
  have hweakD : r * x ≤ D := hweak.trans hCD
  exact (harmonic_floor_scalar_iff hr).2 hweakD

/-- The reciprocal profile saturates the harmonic floor exactly. -/
theorem reciprocal_profile_saturates_floor
    {C r : ℝ} (hr : 0 < r) :
    - (C / r) + C / r = 0 := by
  ring

/-- A scalar uniform floor `K` implies a harmonic floor only after paying the
rank factor `r*K`; this records why a common scalar shift is generally stronger
than the weak-L1 harmonic budget. -/
theorem scalar_floor_to_rank_budget
    {x K r : ℝ} (hr0 : 0 ≤ r)
    (hx : x ≤ K) :
    r * x ≤ r * K := by
  exact mul_le_mul_of_nonneg_left hx hr0

#print axioms harmonic_floor_scalar_iff
#print axioms harmonic_floor_mono
#print axioms reciprocal_profile_saturates_floor
#print axioms scalar_floor_to_rank_budget

end RHB111AHarmonicLoewnerFinite
