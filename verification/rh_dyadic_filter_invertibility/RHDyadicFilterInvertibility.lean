import Mathlib

namespace RHDyadicFilterInvertibility

/-- The elementary forward square estimate used for `D = E - E_half`. -/
theorem sq_sub_le_two_sq_add_two_sq (a b : ℝ) :
    (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a + b)]

/-- The reverse square estimate recovers `E` from `D = E - E_half`. -/
theorem sq_le_two_sq_sub_add_two_sq (a b : ℝ) :
    a ^ 2 ≤ 2 * (a - b) ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - 2 * b)]

/-- Abstract forward weighted-energy ledger. Here `shift` is the weighted
energy of the half-scale error and `q` is the exact post-factor-two scaling
coefficient. -/
theorem forward_energy_transfer
    (hD hE shift boundary q : ℝ)
    (hshift : 2 * shift = q * (hE + boundary))
    (hforward : hD ≤ 2 * hE + 2 * shift) :
    hD ≤ (2 + q) * hE + q * boundary := by
  rw [hshift] at hforward
  nlinarith

/-- Abstract reverse ledger before division by the positive absorption
margin. -/
theorem reverse_energy_absorption
    (hD hE shift boundary q : ℝ)
    (hshift : 2 * shift = q * (hE + boundary))
    (hreverse : hE ≤ 2 * hD + 2 * shift) :
    (1 - q) * hE ≤ 2 * hD + q * boundary := by
  rw [hshift] at hreverse
  nlinarith

/-- A strict contraction coefficient gives a positive absorption margin. -/
theorem positive_absorption_margin
    (q : ℝ)
    (hq : q < 1) :
    0 < 1 - q := by
  linarith

/-- Once the absorption margin is positive, the reverse ledger gives an
explicit finite upper bound for the original energy. -/
theorem recovered_energy_bound
    (hD hE boundary q : ℝ)
    (hq : q < 1)
    (hledger : (1 - q) * hE ≤ 2 * hD + q * boundary) :
    hE ≤ (2 * hD + q * boundary) / (1 - q) := by
  exact (le_div_iff₀ (sub_pos.mpr hq)).2 hledger

/-- A nonzero complex denominator and nonzero numerator produce a nonzero
Mellin filter quotient. -/
theorem nonzero_filter_quotient
    (s z : ℂ)
    (hs : s ≠ 0)
    (hz : z ≠ 1) :
    (1 - z) / s ≠ 0 := by
  exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hz)) hs

#print axioms RHDyadicFilterInvertibility.sq_sub_le_two_sq_add_two_sq
#print axioms RHDyadicFilterInvertibility.sq_le_two_sq_sub_add_two_sq
#print axioms RHDyadicFilterInvertibility.forward_energy_transfer
#print axioms RHDyadicFilterInvertibility.reverse_energy_absorption
#print axioms RHDyadicFilterInvertibility.positive_absorption_margin
#print axioms RHDyadicFilterInvertibility.recovered_energy_bound
#print axioms RHDyadicFilterInvertibility.nonzero_filter_quotient

end RHDyadicFilterInvertibility
