import Mathlib

namespace YMPlaquetteRayleighFinite

/-- A local variance remains uniformly positive if it stays within half of a
    positive reference variance. -/
theorem variance_lower_of_abs_close
    {v v₀ : ℝ}
    (hv₀ : 0 ≤ v₀)
    (hclose : |v - v₀| ≤ v₀ / 2) :
    v₀ / 2 ≤ v := by
  have hlow : -(v₀ / 2) ≤ v - v₀ := (abs_le.mp hclose).1
  linarith

/-- The scalar endpoint of the double-commutator Rayleigh budget. -/
theorem rayleigh_upper_of_double_commutator
    {v r D : ℝ}
    (hv : 0 < v)
    (hbudget : 2 * v * r ≤ D) :
    r ≤ D / (2 * v) := by
  have hden : 0 < 2 * v := by linarith
  apply (le_div_iff₀ hden).2
  nlinarith

/-- A Rayleigh upper bound has the correct direction for a lower bound on the
    normalized Euclidean-time exponential. -/
theorem exp_lower_of_rayleigh_upper
    {t R M : ℝ}
    (ht : 0 ≤ t)
    (hRM : R ≤ M) :
    Real.exp (-t * M) ≤ Real.exp (-t * R) := by
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A positive-time exponential sandwich forces the lower spectral edge to be
    no larger than the finite witness energy. -/
theorem mass_upper_of_exp_sandwich
    {t m M : ℝ}
    (ht : 0 < t)
    (hsandwich : Real.exp (-t * M) ≤ Real.exp (-t * m)) :
    m ≤ M := by
  have hlog : -t * M ≤ -t * m := Real.exp_le_exp.mp hsandwich
  nlinarith

/-- Two-sided dimensionless spectral control plus a two-sided physical
    prefactor gives a two-sided physical mass window. -/
theorem physical_mass_window
    {z δ z₋ z₊ δ₋ δ₊ : ℝ}
    (hz₋0 : 0 ≤ z₋)
    (hz₋ : z₋ ≤ z)
    (hz₊ : z ≤ z₊)
    (hδ₋0 : 0 ≤ δ₋)
    (hδ₋ : δ₋ ≤ δ)
    (hδ₊ : δ ≤ δ₊) :
    z₋ * δ₋ ≤ z * δ ∧ z * δ ≤ z₊ * δ₊ := by
  have hz0 : 0 ≤ z := le_trans hz₋0 hz₋
  have hz₊0 : 0 ≤ z₊ := le_trans hz0 hz₊
  have hδ0 : 0 ≤ δ := le_trans hδ₋0 hδ₋
  constructor
  · calc
      z₋ * δ₋ ≤ z * δ₋ := mul_le_mul_of_nonneg_right hz₋ hδ₋0
      _ ≤ z * δ := mul_le_mul_of_nonneg_left hδ₋ hz0
  · calc
      z * δ ≤ z₊ * δ := mul_le_mul_of_nonneg_right hz₊ hδ0
      _ ≤ z₊ * δ₊ := mul_le_mul_of_nonneg_left hδ₊ hz₊0

/-- Transport error smaller than the endpoint correlation margin leaves a
    strictly positive continuum witness. -/
theorem witness_survives_transport
    {c ε : ℝ}
    (hc : 0 < c)
    (hε0 : 0 ≤ ε)
    (hε : ε < c) :
    0 < c - ε := by
  linarith

#print axioms variance_lower_of_abs_close
#print axioms rayleigh_upper_of_double_commutator
#print axioms exp_lower_of_rayleigh_upper
#print axioms mass_upper_of_exp_sandwich
#print axioms physical_mass_window
#print axioms witness_survives_transport

end YMPlaquetteRayleighFinite
