import Mathlib

/-!
# Faizal--Shabir one-interaction cumulant firewall

Finite scalar countermodel for the step in arXiv:2606.19362v1 Proposition 10.3
around Eqs. (10.29)--(10.31), where the `m = 0` and `m = 1` interaction terms
are removed from the connected `n >= 2` cumulant estimate after vacuum and
one-point centering.

The finite model uses a centered three-point random variable X in {-1,0,1}
with equal base weights and an even interaction W = X^2.  Reweight by
`1 + t W` and normalize.  Symmetry keeps the one-point function exactly zero,
but the normalized connected two-point function (the variance) is

  2 (1+t) / (3+2t)

rather than the base value 2/3.  Its exact difference is

  2t / [3(3+2t)],

which has a nonzero term linear in the interaction parameter t.

Therefore normalization of the vacuum and centering of the one-point function
do not, as a matter of general connected-cumulant algebra, eliminate every
single-interaction contribution to a connected two-point function.  A
model-specific Yang--Mills cancellation could still exist and would itself
need proof.

This file formalizes only the finite rational identity.  It does not formalize
Gaussian integration, BKAR, the Faizal--Shabir polymer expansion, Yang--Mills,
AF/IR identification, OS reconstruction, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirOneInteractionCumulantFirewall

theorem normalized_variance_has_linear_interaction_term
    (t : ℝ)
    (hden : 3 + 2 * t ≠ 0) :
    2 * (1 + t) / (3 + 2 * t) - 2 / 3 =
      2 * t / (3 * (3 + 2 * t)) := by
  field_simp [hden]
  ring

theorem explicit_one_interaction_connected_two_point :
    2 * (1 + ((1 : ℝ) / 10)) / (3 + 2 * ((1 : ℝ) / 10)) - 2 / 3 =
      (1 : ℝ) / 48 := by
  norm_num

#print axioms normalized_variance_has_linear_interaction_term
#print axioms explicit_one_interaction_connected_two_point

end Millennium.YangMills.FaizalShabirOneInteractionCumulantFirewall
