import Mathlib

/-!
# Giga-Miura high-high defect to filtered-separation budget

Finite real algebra only.

If two actual direction vectors have separation delta and filtering changes each
direction by at most 2*eps, then the filtered directions retain at least
delta - 4*eps separation. If 8*eps <= delta, at least half the gap survives.

This file does not formalize vector normalization, convolution, Giga-Miura, Yu,
vorticity, Navier-Stokes, or a Clay statement.
-/

namespace NSGMFilteredSeparationBudget

theorem separation_after_two_errors
    (delta rawSep filtSep errA errB : Real)
    (hraw : delta <= rawSep)
    (htriangle : rawSep <= errA + filtSep + errB) :
    delta - errA - errB <= filtSep := by
  linarith

theorem four_eps_separation_budget
    (delta eps rawSep filtSep errA errB : Real)
    (hraw : delta <= rawSep)
    (htriangle : rawSep <= errA + filtSep + errB)
    (herrA : errA <= 2 * eps)
    (herrB : errB <= 2 * eps) :
    delta - 4 * eps <= filtSep := by
  linarith

theorem eight_eps_preserves_half_gap
    (delta eps : Real)
    (heps : 8 * eps <= delta) :
    delta / 2 <= delta - 4 * eps := by
  linarith

theorem filtered_separation_survives_half
    (delta eps rawSep filtSep errA errB : Real)
    (hraw : delta <= rawSep)
    (htriangle : rawSep <= errA + filtSep + errB)
    (herrA : errA <= 2 * eps)
    (herrB : errB <= 2 * eps)
    (heps : 8 * eps <= delta) :
    delta / 2 <= filtSep := by
  have hfour : delta - 4 * eps <= filtSep :=
    four_eps_separation_budget delta eps rawSep filtSep errA errB
      hraw htriangle herrA herrB
  exact (eight_eps_preserves_half_gap delta eps heps).trans hfour

#print axioms separation_after_two_errors
#print axioms four_eps_separation_budget
#print axioms eight_eps_preserves_half_gap
#print axioms filtered_separation_survives_half

end NSGMFilteredSeparationBudget
