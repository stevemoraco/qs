import Mathlib

/-!
# P-versus-NP variable-clock arithmetic firewall

Finite arithmetic only. This certifies the elementary inequalities used by the
paper-level EXP-completeness obstruction for unary variable-exponent bounded
acceptance. It does NOT formalize complexity classes, reductions, EXP
completeness, or P versus NP.
-/

namespace Millennium.PNP.VariableClockArithmetic

theorem exp_clock_fits_variable_polynomial_clock
    (n c : ℕ) (hn : 2 ≤ n) :
    2 ^ (n ^ c) ≤ n ^ (n ^ c) := by
  exact pow_le_pow_left' hn (n ^ c)

theorem variable_clock_bounded_by_total_length
    (n i N : ℕ) (hn : n ≤ N) (hi : i ≤ N) (hN : 1 ≤ N) :
    n ^ i ≤ N ^ N := by
  exact pow_le_pow hn hN hi

theorem exponential_clock_sandwich
    (n c N : ℕ) (hn2 : 2 ≤ n) (hnN : n ≤ N)
    (hexp : n ^ c ≤ N) (hN : 1 ≤ N) :
    2 ^ (n ^ c) ≤ N ^ N := by
  calc
    2 ^ (n ^ c) ≤ n ^ (n ^ c) := exp_clock_fits_variable_polynomial_clock n c hn2
    _ ≤ N ^ N := variable_clock_bounded_by_total_length n (n ^ c) N hnN hexp hN

#print axioms exp_clock_fits_variable_polynomial_clock
#print axioms variable_clock_bounded_by_total_length
#print axioms exponential_clock_sandwich

end Millennium.PNP.VariableClockArithmetic
