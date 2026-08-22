import Mathlib

namespace RHConnesRayleighGap

/--
Scalar core of the Rayleigh--Ritz ground-state overlap estimate.  The variable
`t` represents the squared overlap with the normalized ground state.
-/
theorem rayleigh_gap_overlap
    (lam0 lam1 mu t : ℝ)
    (hgap : lam0 < lam1)
    (hmix : lam0 * t + lam1 * (1 - t) ≤ mu) :
    1 - t ≤ (mu - lam0) / (lam1 - lam0) := by
  apply (le_div_iff₀ (sub_pos.mpr hgap)).2
  nlinarith

/--
Certified lower/upper spectral enclosures compose with the Rayleigh mixture
bound.  This is the finite scalar core of the interval certificate in the note.
-/
theorem interval_rayleigh_certificate
    (e0m e0p e1m mplus lam0 lam1 mu t : ℝ)
    (ht : t ≤ 1)
    (hcertGap : e0p < e1m)
    (hLam0Lower : e0m ≤ lam0)
    (hLam0Upper : lam0 ≤ e0p)
    (hLam1Lower : e1m ≤ lam1)
    (hMuUpper : mu ≤ mplus)
    (hmix : lam0 * t + lam1 * (1 - t) ≤ mu) :
    1 - t ≤ (mplus - e0m) / (e1m - e0p) := by
  have hscale : 0 ≤ 1 - t := sub_nonneg.mpr ht
  have hgapCompare : e1m - e0p ≤ lam1 - lam0 := by
    linarith
  have hmix' : (lam1 - lam0) * (1 - t) ≤ mu - lam0 := by
    nlinarith
  have hcert : (e1m - e0p) * (1 - t) ≤ mplus - e0m := by
    calc
      (e1m - e0p) * (1 - t)
          ≤ (lam1 - lam0) * (1 - t) :=
            mul_le_mul_of_nonneg_right hgapCompare hscale
      _ ≤ mu - lam0 := hmix'
      _ ≤ mplus - e0m := by linarith
  apply (le_div_iff₀ (sub_pos.mpr hcertGap)).2
  simpa [mul_comm] using hcert

/-- Squared overlap loss controls the phase-aligned squared chord distance. -/
theorem overlap_loss_controls_distance
    (c r : ℝ)
    (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1)
    (hloss : 1 - c ^ 2 ≤ r) :
    2 * (1 - c) ≤ 2 * r := by
  have hsq : c ^ 2 ≤ c := by nlinarith
  nlinarith

/--
Exact finite countermodel: zero Rayleigh value is compatible with zero ground
state overlap when the operator has a lower negative eigenvalue.
-/
theorem zero_rayleigh_can_miss_ground :
    ((-1 : ℝ) * 0 + 0 * (1 - 0) = 0) ∧ (1 - 0 = 1) := by
  norm_num

/--
Even for a positive operator, an arbitrarily small exact excited eigenvalue can
remain orthogonal to the ground state when the first gap collapses.
-/
theorem positive_small_rayleigh_can_miss_ground (eps : ℝ) :
    0 * 0 + eps * (1 - 0) = eps ∧ (1 - 0 = 1) := by
  constructor <;> ring

#print axioms RHConnesRayleighGap.rayleigh_gap_overlap
#print axioms RHConnesRayleighGap.interval_rayleigh_certificate
#print axioms RHConnesRayleighGap.overlap_loss_controls_distance
#print axioms RHConnesRayleighGap.zero_rayleigh_can_miss_ground
#print axioms RHConnesRayleighGap.positive_small_rayleigh_can_miss_ground

end RHConnesRayleighGap
