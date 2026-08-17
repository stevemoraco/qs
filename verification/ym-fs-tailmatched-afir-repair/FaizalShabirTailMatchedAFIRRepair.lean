import Mathlib

/-!
# Faizal--Shabir AF/IR tail-matching and Gram-monotonicity firewalls

Finite algebra supporting two load-bearing repairs in the hard audit of
arXiv:2606.19362v1.

1. Positivity of every member of a Gram family does not imply that the family
   is monotone in an interpolation parameter. Hence positivity of a BKAR/
   coupling-interpolated Gram operator does not, by itself, prove that the
   interpolation derivative or integrated increment is positive.

2. An additive AF/IR comparison can genuinely vanish when one has a signed
   equality and fixes the initial/matching constant by the full future error
   tail. Then the finite-scale discrepancy is exactly the remaining tail.

This file does not formalize Yang--Mills theory, RG maps, Schwinger functions,
the two-loop beta function, Lambda_YM, OS reconstruction, or any Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirTailMatchedAFIRRepair

/-- Two positive Gram values can have a strictly negative increment. -/
theorem positive_gram_values_do_not_force_positive_increment :
    0 ≤ (1 : ℝ) ^ 2 ∧
      0 ≤ ((1 : ℝ) / 2) ^ 2 ∧
      (((1 : ℝ) / 2) ^ 2 - (1 : ℝ) ^ 2) < 0 := by
  norm_num

/-- Exact signed matching turns a finite prefix into minus the remaining tail. -/
theorem matched_total_error_turns_prefix_into_tail
    (d0 prefix tail dK : ℝ)
    (hmatch : d0 + prefix + tail = 0)
    (hprefix : dK = d0 + prefix) :
    dK = -tail := by
  linarith

/-- An interval bound on the remaining tail transfers to the matched discrepancy. -/
theorem matched_tail_interval_controls_discrepancy
    (d0 prefix tail dK rho : ℝ)
    (hmatch : d0 + prefix + tail = 0)
    (hprefix : dK = d0 + prefix)
    (htailLo : -rho ≤ tail)
    (htailHi : tail ≤ rho) :
    -rho ≤ dK ∧ dK ≤ rho := by
  have hd : dK = -tail :=
    matched_total_error_turns_prefix_into_tail d0 prefix tail dK hmatch hprefix
  constructor <;> rw [hd] <;> linarith

/-- Exact-zero tail gives exact AF/IR matching at the corresponding scale. -/
theorem zero_remaining_tail_gives_exact_match
    (d0 prefix dK : ℝ)
    (hmatch : d0 + prefix = 0)
    (hprefix : dK = d0 + prefix) :
    dK = 0 := by
  linarith

#print axioms positive_gram_values_do_not_force_positive_increment
#print axioms matched_total_error_turns_prefix_into_tail
#print axioms matched_tail_interval_controls_discrepancy
#print axioms zero_remaining_tail_gives_exact_match

end Millennium.YangMills.FaizalShabirTailMatchedAFIRRepair
