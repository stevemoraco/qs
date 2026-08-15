import Mathlib

/-!
# Pineau--Vicol intermediate-RSS angular interpolation firewall

Finite scalar algebra only.  These statements isolate the arithmetic needed by
one human PDE synthesis for rotated backward self-similar Navier--Stokes
profiles:

* a lower bound on rotation activity, combined with an angular interpolation
  inequality, forces a lower bound on non-axisymmetric amplitude once the
  second-angular-derivative norm is bounded;
* confining the rotation speed to a compact interval makes that lower bound
  uniform;
* an upper second-derivative budget also forces a fixed fraction of first
  angular-derivative activity into a finite low-frequency band;
* without a curvature/second-derivative cap, the same interpolation inequality
  is compatible with arbitrarily small amplitude.

This file does NOT formalize Pineau--Vicol, cylindrical coordinates, Fourier
series, weighted Sobolev interpolation, Navier--Stokes, or a Millennium Prize
statement.
-/

namespace NSPVAngularInterpolationFloor

/-- If `c` is a lower rotation-activity scale, `r` the first angular derivative,
`a` the non-axisymmetric amplitude, and `k` a second-derivative scale, then
`c ≤ alpha*r` and `r² ≤ a*k` imply the product lower bound
`c² ≤ alpha²*a*k`. -/
theorem rotation_activity_forces_asymmetry_product
    {c alpha r a k : ℝ}
    (hc : 0 ≤ c) (halpha : 0 ≤ alpha) (hr : 0 ≤ r)
    (ha : 0 ≤ a) (hk : 0 ≤ k)
    (hrot : c ≤ alpha * r)
    (hinterp : r ^ 2 ≤ a * k) :
    c ^ 2 ≤ alpha ^ 2 * (a * k) := by
  have hdiff : 0 ≤ alpha * r - c := sub_nonneg.mpr hrot
  have hsum : 0 ≤ alpha * r + c :=
    add_nonneg (mul_nonneg halpha hr) hc
  have hsq : c ^ 2 ≤ (alpha * r) ^ 2 := by
    nlinarith [mul_nonneg hdiff hsum]
  have hscale : alpha ^ 2 * r ^ 2 ≤ alpha ^ 2 * (a * k) :=
    mul_le_mul_of_nonneg_left hinterp (sq_nonneg alpha)
  calc
    c ^ 2 ≤ (alpha * r) ^ 2 := hsq
    _ = alpha ^ 2 * r ^ 2 := by ring
    _ ≤ alpha ^ 2 * (a * k) := hscale

/-- Once `alpha` and the curvature scale `k` are bounded above by `A` and `K`,
the activity lower bound forces a uniform amplitude product floor. -/
theorem compact_rotation_window_forces_uniform_product
    {c alpha A r a k K : ℝ}
    (hc : 0 ≤ c) (halpha : 0 ≤ alpha) (hA : alpha ≤ A)
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hk : 0 ≤ k) (hkK : k ≤ K)
    (hrot : c ≤ alpha * r)
    (hinterp : r ^ 2 ≤ a * k) :
    c ^ 2 ≤ A ^ 2 * (a * K) := by
  have hA0 : 0 ≤ A := le_trans halpha hA
  have hbase : c ^ 2 ≤ alpha ^ 2 * (a * k) :=
    rotation_activity_forces_asymmetry_product
      hc halpha hr ha hk hrot hinterp
  have hdiff : 0 ≤ A - alpha := sub_nonneg.mpr hA
  have hsum : 0 ≤ A + alpha := add_nonneg hA0 halpha
  have halpha_sq : alpha ^ 2 ≤ A ^ 2 := by
    nlinarith [mul_nonneg hdiff hsum]
  have hak : a * k ≤ a * K := mul_le_mul_of_nonneg_left hkK ha
  have hprod : alpha ^ 2 * (a * k) ≤ A ^ 2 * (a * K) :=
    mul_le_mul halpha_sq hak (mul_nonneg ha hk) (sq_nonneg A)
  exact hbase.trans hprod

/-- With positive upper bounds, the preceding product estimate is an explicit
lower bound on the non-axisymmetric amplitude. -/
theorem explicit_uniform_asymmetry_floor
    {c A a K : ℝ}
    (hA : 0 < A) (hK : 0 < K)
    (hprod : c ^ 2 ≤ A ^ 2 * (a * K)) :
    c ^ 2 / (A ^ 2 * K) ≤ a := by
  have hden : 0 < A ^ 2 * K := mul_pos (sq_pos_of_pos hA) hK
  apply (div_le_iff₀ hden).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using hprod

/-- Abstract Fourier-tail gate: if a cutoff `N` makes the curvature budget
`K²` at most half of `N² r0²`, then any tail obeying `N²*tail ≤ K²` contains at
most half of the required first-derivative activity. -/
theorem curvature_cap_forces_half_activity_tail
    {K N r0 tail : ℝ}
    (hN : 0 < N)
    (htailK : N ^ 2 * tail ≤ K ^ 2)
    (hchoice : 2 * K ^ 2 ≤ N ^ 2 * r0 ^ 2) :
    2 * tail ≤ r0 ^ 2 := by
  have hN2 : 0 < N ^ 2 := sq_pos_of_pos hN
  have hmul : N ^ 2 * (2 * tail) ≤ N ^ 2 * r0 ^ 2 := by
    nlinarith [htailK, hchoice]
  exact (mul_le_mul_left hN2).mp hmul

/-- If total first-derivative activity is at least `r0²` and the high-frequency
tail is at most half that amount, then the complementary low band carries at
least half the activity. -/
theorem half_activity_tail_forces_low_band
    {total low tail r0 : ℝ}
    (hdecomp : total = low + tail)
    (hfloor : r0 ^ 2 ≤ total)
    (htail : 2 * tail ≤ r0 ^ 2) :
    r0 ^ 2 / 2 ≤ low := by
  nlinarith

/-- The curvature cap is load-bearing: for every positive `eps`, a unit first
angular derivative is compatible with interpolation amplitude `eps` if the
second-derivative scale is allowed to grow like `1/eps`. -/
theorem no_curvature_cap_allows_small_amplitude
    {eps : ℝ} (heps : 0 < eps) :
    (1 : ℝ) ^ 2 = eps * (1 / eps) := by
  have hne : eps ≠ 0 := ne_of_gt heps
  field_simp [hne]

#print axioms rotation_activity_forces_asymmetry_product
#print axioms compact_rotation_window_forces_uniform_product
#print axioms explicit_uniform_asymmetry_floor
#print axioms curvature_cap_forces_half_activity_tail
#print axioms half_activity_tail_forces_low_band
#print axioms no_curvature_cap_allows_small_amplitude

end NSPVAngularInterpolationFloor
