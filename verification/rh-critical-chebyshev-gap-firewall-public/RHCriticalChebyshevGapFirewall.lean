import Mathlib

namespace RHCriticalChebyshevGapFirewall

noncomputable def margin (s theta A c : ℝ) : ℝ :=
  s + theta / s - c - A

/-- Exact change of the frozen gap margin between two positive square-root
coordinates. -/
theorem gap_increment_identity
    {a b theta A c : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    margin b theta A c - margin a theta A c =
      (b - a) * (1 - theta / (a * b)) := by
  unfold margin
  field_simp [ha, hb]
  ring

/-- At a critical point `theta = r^2`, the left endpoint exceeds the
interior value by the exact square loss `(r-a)^2/a`. -/
theorem left_endpoint_loss
    {a r theta A c : ℝ}
    (ha : a ≠ 0)
    (htheta : theta = r ^ 2) :
    margin a theta A c = margin r theta A c + (r - a) ^ 2 / a := by
  rw [htheta]
  unfold margin
  field_simp [ha]
  ring

/-- Symmetric right-endpoint loss identity. -/
theorem right_endpoint_loss
    {b r theta A c : ℝ}
    (hb : b ≠ 0)
    (htheta : theta = r ^ 2) :
    margin b theta A c = margin r theta A c + (b - r) ^ 2 / b := by
  rw [htheta]
  unfold margin
  field_simp [hb]
  ring

/-- The initial prime boundary is exactly zero: the prime jump contribution
cancels and the deterministic boundary constant cancels the square root. -/
theorem initial_boundary_zero
    {s ell : ℝ} (hs : s ≠ 0) :
    margin s ell (ell / s) s = 0 := by
  unfold margin
  field_simp [hs]
  ring

/-- Exact rational countermodel: both endpoints are positive while the unique
critical interior value is negative. -/
theorem endpoint_sampling_can_miss_interior :
    0 < margin 2 9 (61 / 10) 0 ∧
    0 < margin 4 9 (61 / 10) 0 ∧
    margin 3 9 (61 / 10) 0 < 0 := by
  norm_num [margin]

#print axioms gap_increment_identity
#print axioms left_endpoint_loss
#print axioms right_endpoint_loss
#print axioms initial_boundary_zero
#print axioms endpoint_sampling_can_miss_interior

end RHCriticalChebyshevGapFirewall
