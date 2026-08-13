import Mathlib

/-!
# Real equal-shell triad: normalized leakage-floor finite core

This file formalizes only the cleared-denominator scalar inequality behind
`NS_THREE_MODE_NORMALIZED_LEAKAGE_FLOOR_2026-08-13.md`.

For high polarizations `(h,-K,c)` and `(h,K,-c)`, let
`D² = K²+h²+c²`.  After unit normalization, the desired high-high coefficient
has magnitude `|4Khc|/D²` while either vertical low-high outer coefficient has
magnitude `|2Kh|/D`.  Clearing the positive denominator reduces
`C_des² ≤ 4 C_out²` to the polynomial inequality below.

No Fourier analysis, Leray projection, localization, Navier--Stokes solution,
or blowup theorem is represented here.
-/

namespace NSBraid
namespace RealEqualShellTriadLeakageFloor

/-- The high-polarization squared norm dominates the free vertical-coordinate
square. -/
theorem normSq_ge_verticalSq (K h c : ℝ) :
    c ^ 2 ≤ K ^ 2 + h ^ 2 + c ^ 2 := by
  nlinarith [sq_nonneg K, sq_nonneg h]

/-- Cleared-denominator form of the normalized leakage floor
`C_des² ≤ 4 C_out²`.

The left side is the square of the desired numerator `4Khc`; the right side
is four times the outer numerator square `(2Kh)²`, multiplied by the common
high-polarization norm square. -/
theorem desiredSq_le_four_outerSq_cleared (K h c : ℝ) :
    (4 * K * h * c) ^ 2 ≤
      4 * (2 * K * h) ^ 2 * (K ^ 2 + h ^ 2 + c ^ 2) := by
  have hbase : c ^ 2 ≤ K ^ 2 + h ^ 2 + c ^ 2 :=
    normSq_ge_verticalSq K h c
  have hfactor : 0 ≤ (4 * K * h) ^ 2 := sq_nonneg (4 * K * h)
  have hmul := mul_le_mul_of_nonneg_left hbase hfactor
  nlinarith [hmul]

/-- The gap above the sharp factor-four bound is exactly a manifestly
nonnegative polynomial. -/
theorem leakageFloor_gap_identity (K h c : ℝ) :
    4 * (2 * K * h) ^ 2 * (K ^ 2 + h ^ 2 + c ^ 2)
      - (4 * K * h * c) ^ 2
    = 16 * K ^ 2 * h ^ 2 * (K ^ 2 + h ^ 2) := by
  ring

/-- Consequently the cleared leakage-floor gap is nonnegative. -/
theorem leakageFloor_gap_nonneg (K h c : ℝ) :
    0 ≤
      4 * (2 * K * h) ^ 2 * (K ^ 2 + h ^ 2 + c ^ 2)
        - (4 * K * h * c) ^ 2 := by
  rw [leakageFloor_gap_identity]
  positivity

#print axioms normSq_ge_verticalSq
#print axioms desiredSq_le_four_outerSq_cleared
#print axioms leakageFloor_gap_identity
#print axioms leakageFloor_gap_nonneg

end RealEqualShellTriadLeakageFloor
end NSBraid
