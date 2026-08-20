import Mathlib

namespace Millennium.YangMills.FaizalShabirEntryFirstOrderFirewall

theorem linear_term_dominates_quadratic_at_small_g
    (a A g : ℝ)
    (hg : 0 < g)
    (hsmall : A * g < a) :
    A * g ^ 2 < a * g := by
  have h := mul_lt_mul_of_pos_right hsmall hg
  simpa [pow_two, mul_assoc] using h

theorem first_order_remainder_blocks_quadratic_entry
    (a A c g r : ℝ)
    (hg : 0 < g)
    (hr : -(c * g ^ 2) ≤ r)
    (hsmall : (A + c) * g < a) :
    A * g ^ 2 < a * g + r := by
  have h := mul_lt_mul_of_pos_right hsmall hg
  have hmain : (A + c) * g ^ 2 < a * g := by
    simpa [pow_two, mul_assoc] using h
  linarith

theorem exact_linear_entry_blocks_quadratic_bound
    (a A g : ℝ)
    (hg : 0 < g)
    (hsmall : A * g < a) :
    A * g ^ 2 < a * g :=
  linear_term_dominates_quadratic_at_small_g a A g hg hsmall

#print axioms linear_term_dominates_quadratic_at_small_g
#print axioms first_order_remainder_blocks_quadratic_entry
#print axioms exact_linear_entry_blocks_quadratic_bound

end Millennium.YangMills.FaizalShabirEntryFirstOrderFirewall
