import Mathlib

/-!
Finite algebraic core of the BSD Kurihara/Fitting curvature correction.

Arithmetic input (not formalized here): Angurel, Cor. 3.29 gives
  2*m = min (2*n) (l+r)
for the true Fitting exponent m and neighboring/raw Kurihara exponents l,n,r.
The theorem below extracts the exact doubled correction without division.
-/

namespace BSDBraid
namespace KuriharaCurvature

/-- If the doubled true exponent is the smaller of the raw doubled exponent
and the neighboring sum, then the doubled correction is exactly the positive
part of the raw discrete concavity defect.  Nat subtraction already implements
that positive part. -/
theorem doubled_curvature_correction
    (l n r m : ℕ)
    (hm : 2 * m = min (2 * n) (l + r)) :
    2 * (n - m) = 2 * n - (l + r) := by
  by_cases h : 2 * n ≤ l + r
  · have hmin : min (2 * n) (l + r) = 2 * n := min_eq_left h
    rw [hmin] at hm
    have hmn : m = n := by omega
    simp [hmn, h]
  · have hlt : l + r < 2 * n := Nat.lt_of_not_ge h
    have hmin : min (2 * n) (l + r) = l + r := min_eq_right (Nat.le_of_lt hlt)
    rw [hmin] at hm
    omega

/-- Positive curvature is exactly strict downward correction of the raw
exponent. -/
theorem curvature_positive_iff_strict_correction
    (l n r m : ℕ)
    (hm : 2 * m = min (2 * n) (l + r)) :
    0 < 2 * n - (l + r) ↔ m < n := by
  by_cases h : 2 * n ≤ l + r
  · have hmin : min (2 * n) (l + r) = 2 * n := min_eq_left h
    rw [hmin] at hm
    have hmn : m = n := by omega
    simp [hmn, h]
  · have hlt : l + r < 2 * n := Nat.lt_of_not_ge h
    have hmin : min (2 * n) (l + r) = l + r := min_eq_right (Nat.le_of_lt hlt)
    rw [hmin] at hm
    omega

/-- The positive curvature defect is automatically even. -/
theorem curvature_even
    (l n r m : ℕ)
    (hm : 2 * m = min (2 * n) (l + r)) :
    Even (2 * n - (l + r)) := by
  rw [← doubled_curvature_correction l n r m hm]
  exact ⟨n - m, by omega⟩

/-- Consecutive Smith/Fitting differences inherit only the difference of the
local doubled curvature corrections. -/
theorem adjacent_difference_transfer
    (n0 n1 m0 m1 k0 k1 : ℤ)
    (h0 : 2 * (n0 - m0) = k0)
    (h1 : 2 * (n1 - m1) = k1) :
    2 * (m0 - m1) = 2 * (n0 - n1) - k0 + k1 := by
  linarith

end KuriharaCurvature
end BSDBraid
