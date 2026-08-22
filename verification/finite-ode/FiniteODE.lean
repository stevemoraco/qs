import Mathlib

namespace FiniteODE

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

theorem nonzero_product_derivative
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

theorem finite_multiplier_preserves_bound
    {g e d : ℝ}
    (hg : 0 < g)
    (he : e < d / g) :
    g * e < d := by
  have h := (lt_div_iff₀ hg).mp he
  nlinarith [h]

theorem finite_multiplier_tail_bound
    (seed : ℕ → ℝ)
    {g d : ℝ}
    (hg : 0 < g)
    (N : ℕ)
    (htail : ∀ n ≥ N, seed n < d / g) :
    ∀ n ≥ N, g * seed n < d := by
  intro n hn
  exact finite_multiplier_preserves_bound hg (htail n hn)

#print axioms conserved_quadratic_form
#print axioms second_quadratic_form
#print axioms nonzero_product_derivative
#print axioms finite_multiplier_preserves_bound
#print axioms finite_multiplier_tail_bound

end FiniteODE
