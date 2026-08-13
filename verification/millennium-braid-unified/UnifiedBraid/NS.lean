import Mathlib

namespace MillenniumBraidUnified
namespace NSCore

theorem conserved_quadratic_form
    {a b c l m x y z dx dy dz : ℝ}
    (ha : a = b + c)
    (hx : dx = -a * l * m * y * z)
    (hy : dy = b * l * m * x * z)
    (hz : dz = c * l * m * x * y) :
    2 * x * dx + 2 * y * dy + 2 * z * dz = 0 := by
  rw [hx, hy, hz, ha]
  ring

theorem second_quadratic_form
    {b c l m x y z dy dz : ℝ}
    (hy : dy = b * l * m * x * z)
    (hz : dz = c * l * m * x * y) :
    2 * c * y * dy - 2 * b * z * dz = 0 := by
  rw [hy, hz]
  ring

theorem pump_zero_transversality
    {a l m y z : ℝ}
    (ha : a ≠ 0)
    (hl : l ≠ 0)
    (hm : m ≠ 0)
    (hy : y ≠ 0)
    (hz : z ≠ 0) :
    -a * l * m * y * z ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (neg_ne_zero.mpr ha) hl)
        hm)
      hy)
    hz

theorem principal_gating_cost_ratio
    {N R N' R' r f : ℝ}
    (hN : N' = r * N)
    (hR : R' ^ 2 = f * R ^ 2) :
    N' * R' ^ 2 = (r * f) * (N * R ^ 2) := by
  rw [hN, hR]
  ring

theorem barrier_beating_implies_gating_growth
    {r f : ℝ}
    (hr : 0 < r)
    (hbeat : (1 : ℝ) / r < f) :
    1 < r * f := by
  have hmul : (1 : ℝ) < f * r := (div_lt_iff₀ hr).mp hbeat
  simpa [mul_comm] using hmul

theorem finite_multiplier_tail_bound
    (seed : ℕ → ℝ)
    {g d : ℝ}
    (hg : 0 < g)
    (N : ℕ)
    (htail : ∀ n ≥ N, seed n < d / g) :
    ∀ n ≥ N, g * seed n < d := by
  intro n hn
  have h := (lt_div_iff₀ hg).mp (htail n hn)
  nlinarith [h]

end NSCore
end MillenniumBraidUnified
