import BSDGVAsymptoticAggregation

/-!
# Minimal-discriminant scaling algebra for the BSD semiprime family

This module certifies only the exact polynomial and rational-coefficient
identities used when the externally proved natural-height asymptotic is
reparametrized by the minimal discriminant `|Delta_min| = 64 D^3`.

It does not formalize minimal Weierstrass models, prime counting, Selmer groups,
the CM rank-zero converse, or the Birch--Swinnerton-Dyer conjecture.
-/

namespace BSDGVSemiprimeDensity

/-- The short-Weierstrass discriminant polynomial for
`y^2 = x^3 - D*x` simplifies to `64*D^3`. -/
theorem short_weierstrass_discriminant (D : ℤ) :
    -16 * (4 * (-D) ^ 3 + 27 * (0 : ℤ) ^ 2) = 64 * D ^ 3 := by
  ring

/-- Replacing `D <= X` by `64*D^3 <= H` multiplies the leading
natural-height coefficient by `3/4`. -/
theorem discriminant_height_density_coefficient :
    (7 / 32 : ℚ) * (3 / 4) = 21 / 128 := by
  norm_num

/-- Positive Legendre-sign sector after minimal-discriminant scaling. -/
theorem positive_sector_discriminant_coefficient :
    (1 / 32 : ℚ) * (3 / 4) = 3 / 128 := by
  norm_num

/-- Negative Legendre-sign sector after minimal-discriminant scaling. -/
theorem negative_sector_discriminant_coefficient :
    (3 / 16 : ℚ) * (3 / 4) = 9 / 64 := by
  norm_num

/-- The two discriminant-height sign sectors add to the total certified
coefficient. -/
theorem discriminant_sector_sum :
    (3 / 128 : ℚ) + 9 / 64 = 21 / 128 := by
  norm_num

/-- Dividing the certified discriminant-height coefficient by the total
semiprime-family coefficient recovers the relative density `7/32`. -/
theorem discriminant_relative_density_certificate :
    (21 / 128 : ℚ) / (3 / 4) = 7 / 32 := by
  norm_num

/-- Exactly one seventh of the certified coefficient is in the positive
Legendre-sign sector. -/
theorem positive_sector_share_certificate :
    (3 / 128 : ℚ) / (21 / 128) = 1 / 7 := by
  norm_num

/-- Exactly six sevenths of the certified coefficient is in the negative
Legendre-sign sector. -/
theorem negative_sector_share_certificate :
    (9 / 64 : ℚ) / (21 / 128) = 6 / 7 := by
  norm_num

#print axioms short_weierstrass_discriminant
#print axioms discriminant_height_density_coefficient
#print axioms positive_sector_discriminant_coefficient
#print axioms negative_sector_discriminant_coefficient
#print axioms discriminant_sector_sum
#print axioms discriminant_relative_density_certificate
#print axioms positive_sector_share_certificate
#print axioms negative_sector_share_certificate

end BSDGVSemiprimeDensity
