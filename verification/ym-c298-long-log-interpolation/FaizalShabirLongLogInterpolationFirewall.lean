import Mathlib

/-!
# C298 — long-log interpolation determinant firewall

Finite scalar algebra for the 3x3 counterexample used in the C298 reflection-positivity
audit. The matrix/OS interpretation is external to this file.

Endpoint matrix `B` has determinant `43/500 > 0`. The entrywise square-root midpoint
has determinant `-1/2 + 2*s`, where `s >= 0` and `s^2 = 6/125`; this determinant is
strictly negative.

This file does not formalize reflection positivity, transfer operators, Yang–Mills theory,
the mass gap, or the Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirLongLogInterpolationFirewall

theorem endpoint_determinant_positive :
    (0 : ℝ) < 43 / 500 := by
  norm_num

theorem midpoint_determinant_negative
    (s : ℝ)
    (hs0 : 0 ≤ s)
    (hs2 : s^2 = (6 : ℝ) / 125) :
    -(1 : ℝ) / 2 + 2 * s < 0 := by
  have hslt : s < (1 : ℝ) / 4 := by
    nlinarith
  nlinarith

#print axioms endpoint_determinant_positive
#print axioms midpoint_determinant_negative

end Millennium.YangMills.FaizalShabirLongLogInterpolationFirewall
