import Mathlib

namespace RHCriticalChebyshevClampMinimum

/-- The variable part of the critical Chebyshev margin after writing
`x = s^2`. -/
noncomputable def kernel (s theta : ℝ) : ℝ :=
  s + theta / s

/-- The complete frozen prime-gap margin; `A` and `c` are constant on the gap. -/
noncomputable def margin (s theta A c : ℝ) : ℝ :=
  kernel s theta - c - A

/-- Exact factorization comparing a point to the left endpoint. -/
theorem left_difference_identity
    {s l theta : ℝ}
    (hs : s ≠ 0)
    (hl : l ≠ 0) :
    kernel s theta - kernel l theta =
      (s - l) * (s * l - theta) / (s * l) := by
  unfold kernel
  field_simp [hs, hl] ; ring

/-- Exact factorization comparing a point to the right endpoint. -/
theorem right_difference_identity
    {s u theta : ℝ}
    (hs : s ≠ 0)
    (hu : u ≠ 0) :
    kernel s theta - kernel u theta =
      (u - s) * (theta - s * u) / (s * u) := by
  unfold kernel
  field_simp [hs, hu] ; ring

/-- Exact square factorization at an interior critical point `theta = r^2`. -/
theorem interior_difference_identity
    {s r : ℝ}
    (hs : s ≠ 0) :
    kernel s (r ^ 2) - 2 * r = (s - r) ^ 2 / s := by
  unfold kernel
  field_simp [hs] ; ring

/-- If `theta ≤ l^2`, the left endpoint minimizes the kernel on every
point to its right. -/
theorem left_regime_kernel_minimum
    {s l theta : ℝ}
    (hs : 0 < s)
    (hl : 0 < l)
    (hls : l ≤ s)
    (htheta : theta ≤ l ^ 2) :
    kernel l theta ≤ kernel s theta := by
  have hslpos : 0 < s * l := mul_pos hs hl
  have hfirst : 0 ≤ s - l := sub_nonneg.mpr hls
  have hsquare : l ^ 2 ≤ s * l := by
    nlinarith
  have hsecond : 0 ≤ s * l - theta := by
    linarith
  have hquot :
      0 ≤ (s - l) * (s * l - theta) / (s * l) :=
    div_nonneg (mul_nonneg hfirst hsecond) (le_of_lt hslpos)
  rw [← left_difference_identity (ne_of_gt hs) (ne_of_gt hl)] at hquot
  linarith

/-- If `u^2 ≤ theta`, the right endpoint minimizes the kernel on every
point to its left. -/
theorem right_regime_kernel_minimum
    {s u theta : ℝ}
    (hs : 0 < s)
    (hu : 0 < u)
    (hsu : s ≤ u)
    (htheta : u ^ 2 ≤ theta) :
    kernel u theta ≤ kernel s theta := by
  have hsupos : 0 < s * u := mul_pos hs hu
  have hfirst : 0 ≤ u - s := sub_nonneg.mpr hsu
  have hsquare : s * u ≤ u ^ 2 := by
    nlinarith
  have hsecond : 0 ≤ theta - s * u := by
    linarith
  have hquot :
      0 ≤ (u - s) * (theta - s * u) / (s * u) :=
    div_nonneg (mul_nonneg hfirst hsecond) (le_of_lt hsupos)
  rw [← right_difference_identity (ne_of_gt hs) (ne_of_gt hu)] at hquot
  linarith

/-- If `theta = r^2`, the critical point `r` is a global positive-axis
minimum of the kernel. -/
theorem interior_regime_kernel_minimum
    {s r : ℝ}
    (hs : 0 < s) :
    2 * r ≤ kernel s (r ^ 2) := by
  have hquot : 0 ≤ (s - r) ^ 2 / s :=
    div_nonneg (sq_nonneg (s - r)) (le_of_lt hs)
  rw [← interior_difference_identity (ne_of_gt hs)] at hquot
  linarith

/-- Constants frozen on a prime gap do not change the left-endpoint minimum. -/
theorem left_regime_margin_minimum
    {s l theta A c : ℝ}
    (hs : 0 < s)
    (hl : 0 < l)
    (hls : l ≤ s)
    (htheta : theta ≤ l ^ 2) :
    margin l theta A c ≤ margin s theta A c := by
  unfold margin
  linarith [left_regime_kernel_minimum hs hl hls htheta]

/-- Constants frozen on a prime gap do not change the right-endpoint minimum. -/
theorem right_regime_margin_minimum
    {s u theta A c : ℝ}
    (hs : 0 < s)
    (hu : 0 < u)
    (hsu : s ≤ u)
    (htheta : u ^ 2 ≤ theta) :
    margin u theta A c ≤ margin s theta A c := by
  unfold margin
  linarith [right_regime_kernel_minimum hs hu hsu htheta]

/-- Constants frozen on a prime gap do not change the interior critical
minimum. -/
theorem interior_regime_margin_minimum
    {s r A c : ℝ}
    (hs : 0 < s) :
    2 * r - c - A ≤ margin s (r ^ 2) A c := by
  unfold margin
  linarith [interior_regime_kernel_minimum (r := r) hs]

#print axioms left_difference_identity
#print axioms right_difference_identity
#print axioms interior_difference_identity
#print axioms left_regime_kernel_minimum
#print axioms right_regime_kernel_minimum
#print axioms interior_regime_kernel_minimum
#print axioms left_regime_margin_minimum
#print axioms right_regime_margin_minimum
#print axioms interior_regime_margin_minimum

end RHCriticalChebyshevClampMinimum
