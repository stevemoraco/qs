import Mathlib

namespace Millennium.YangMills.FaizalShabirEntryReferenceCenterFirewall

theorem identity_center_recurrence_constant
    (g : ℕ → ℝ)
    (hg0 : g 0 = 1)
    (hrec : ∀ n, g (n + 1) = g n) :
    ∀ n, g n = 1 := by
  intro n
  induction n with
  | zero => exact hg0
  | succ n ih =>
      rw [hrec n, ih]

theorem identity_center_not_quarter_at_two
    (g : ℕ → ℝ)
    (hg0 : g 0 = 1)
    (hrec : ∀ n, g (n + 1) = g n) :
    ¬ (|g 2| ≤ (1 : ℝ) / 4) := by
  have hconst := identity_center_recurrence_constant g hg0 hrec 2
  rw [hconst, abs_one]
  norm_num

theorem nonzero_multiplier_product_does_not_imply_center_decay :
    (1 : ℝ) ≠ 0 ∧ ¬ ((1 : ℝ) ≤ (1 : ℝ) / 4) := by
  constructor <;> norm_num

#print axioms identity_center_recurrence_constant
#print axioms identity_center_not_quarter_at_two
#print axioms nonzero_multiplier_product_does_not_imply_center_decay

end Millennium.YangMills.FaizalShabirEntryReferenceCenterFirewall
