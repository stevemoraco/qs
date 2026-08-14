import Mathlib

/-!
# Yu filtered peak-visibility finite cores

Finite real algebra only.  These lemmas isolate the scale arithmetic behind a
possible high-vorticity coverage repair in the Runlong Yu filtered-vorticity
route.

They do not formalize filter estimates, suitable weak solutions, a singular
profile, a regularity criterion, or Navier--Stokes regularity/blow-up.
-/

namespace NSYuPeakVisibilityDichotomy

/-- If a filtered-vorticity peak is visible at the scale `r^-2 E` while its
Lipschitz constant is bounded at the scale `r^-3 E`, then the half-peak core
has a macroscopic radius.  This multiplicative form avoids introducing square
roots or division into the finite core. -/
theorem peak_visibility_forces_macroscopic_core_scale
    (r E peak L kappa C : ℝ)
    (hr : 0 < r)
    (hkappa : 0 ≤ kappa)
    (hC : 0 ≤ C)
    (hpeak : kappa * E ≤ r ^ 2 * peak)
    (hgrad : r ^ 3 * L ≤ C * E) :
    kappa * r * L ≤ C * peak := by
  have h1 : kappa * (r ^ 3 * L) ≤ kappa * (C * E) :=
    mul_le_mul_of_nonneg_left hgrad hkappa
  have h2 : C * (kappa * E) ≤ C * (r ^ 2 * peak) :=
    mul_le_mul_of_nonneg_left hpeak hC
  have hchain : kappa * (r ^ 3 * L) ≤ C * (r ^ 2 * peak) := by
    calc
      kappa * (r ^ 3 * L) ≤ kappa * (C * E) := h1
      _ = C * (kappa * E) := by ring
      _ ≤ C * (r ^ 2 * peak) := h2
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hscaled : r ^ 2 * (kappa * r * L) ≤ r ^ 2 * (C * peak) := by
    calc
      r ^ 2 * (kappa * r * L) = kappa * (r ^ 3 * L) := by ring
      _ ≤ C * (r ^ 2 * peak) := hchain
      _ = r ^ 2 * (C * peak) := by ring
  nlinarith [hscaled]

/-- Once the preceding scale inequality holds, any radius no larger than the
fixed fraction `kappa*r/(2*C)` lies inside the half-peak Lipschitz core. -/
theorem fixed_fraction_radius_fits_half_peak_core
    (r peak L kappa C s : ℝ)
    (hC : 0 < C)
    (hL : 0 ≤ L)
    (hscale : kappa * r * L ≤ C * peak)
    (hs : 2 * C * s ≤ kappa * r) :
    2 * L * s ≤ peak := by
  have hmul : (2 * C * s) * L ≤ (kappa * r) * L :=
    mul_le_mul_of_nonneg_right hs hL
  have hchain : C * (2 * L * s) ≤ C * peak := by
    calc
      C * (2 * L * s) = (2 * C * s) * L := by ring
      _ ≤ (kappa * r) * L := hmul
      _ = kappa * r * L := by ring
      _ ≤ C * peak := hscale
  nlinarith [hchain]

/-- A Lipschitz lower estimate plus the half-peak radius condition gives a
uniform high-vorticity core. -/
theorem half_peak_survives_on_core
    (peak L s d value : ℝ)
    (hL : 0 ≤ L)
    (hd : d ≤ s)
    (hhalf : 2 * L * s ≤ peak)
    (hlower : peak - L * d ≤ value) :
    peak / 2 ≤ value := by
  have hLd : L * d ≤ L * s := mul_le_mul_of_nonneg_left hd hL
  have hLs : L * s ≤ peak / 2 := by linarith
  linarith

/-- If the dimensionless filtered peak is small, then its square is smaller by
the square of the visibility parameter.  In the PDE application `E^2` is the
local energy amplitude and `r^4*peak^2` is the crude scale of the filtered
enstrophy reservoir. -/
theorem peak_invisibility_gives_quadratic_gain
    (r peak eps E : ℝ)
    (hpeak_nonneg : 0 ≤ peak)
    (heps : 0 ≤ eps)
    (hE : 0 ≤ E)
    (hsmall : r ^ 2 * peak ≤ eps * E) :
    r ^ 4 * peak ^ 2 ≤ eps ^ 2 * E ^ 2 := by
  have hA : 0 ≤ r ^ 2 * peak :=
    mul_nonneg (sq_nonneg r) hpeak_nonneg
  have hB : 0 ≤ eps * E := mul_nonneg heps hE
  have hprod :
      0 ≤ (eps * E - r ^ 2 * peak) * (eps * E + r ^ 2 * peak) :=
    mul_nonneg (sub_nonneg.mpr hsmall) (add_nonneg hB hA)
  calc
    r ^ 4 * peak ^ 2 = (r ^ 2 * peak) ^ 2 := by ring
    _ ≤ (eps * E) ^ 2 := by nlinarith
    _ = eps ^ 2 * E ^ 2 := by ring

/-- Combining the crude cylinder-volume bound with peak invisibility transfers
the quadratic gain directly to the filtered-enstrophy reservoir. -/
theorem filtered_enstrophy_small_of_peak_invisible
    (r peak eps E K O : ℝ)
    (hpeak_nonneg : 0 ≤ peak)
    (heps : 0 ≤ eps)
    (hE : 0 ≤ E)
    (hK : 0 ≤ K)
    (hsmall : r ^ 2 * peak ≤ eps * E)
    (hO : O ≤ K * (r ^ 4 * peak ^ 2)) :
    O ≤ K * (eps ^ 2 * E ^ 2) := by
  have hquad : r ^ 4 * peak ^ 2 ≤ eps ^ 2 * E ^ 2 :=
    peak_invisibility_gives_quadratic_gain
      r peak eps E hpeak_nonneg heps hE hsmall
  exact hO.trans (mul_le_mul_of_nonneg_left hquad hK)

/-- The visible/invisible split is exhaustive at every fixed scale. -/
theorem peak_visibility_dichotomy
    (r peak kappa E : ℝ) :
    kappa * E ≤ r ^ 2 * peak ∨ r ^ 2 * peak < kappa * E := by
  exact le_or_gt (kappa * E) (r ^ 2 * peak)

#print axioms peak_visibility_forces_macroscopic_core_scale
#print axioms fixed_fraction_radius_fits_half_peak_core
#print axioms half_peak_survives_on_core
#print axioms peak_invisibility_gives_quadratic_gain
#print axioms filtered_enstrophy_small_of_peak_invisible
#print axioms peak_visibility_dichotomy

end NSYuPeakVisibilityDichotomy
