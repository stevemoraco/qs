import Mathlib

/-!
# RepSAT padding-projection finite arithmetic firewall

This file formalizes only exact rational error margins and the scaled source
lower-bound arithmetic from the round-42 RepSAT audit. It does not formalize
probability spaces, binomial concentration, parity distributions, Boolean
circuits, circuit restriction, SAT, NP, or P versus NP.
-/

namespace MillenniumBraid
namespace B2Round42PNP

/-- The two selected Bernoulli parity biases have total support density
`223/1000 + 571/1000 = 397/500`. -/
theorem support_density_identity :
    (223 : ℚ) / 1000 + 571 / 1000 = 397 / 500 := by
  norm_num

/-- Weight one is assigned the exact raw two-row miss probability used in the
human proof. -/
theorem weight_one_raw_miss :
    (((1 : ℚ) + 277 / 500) * (1 - 71 / 500)) / 4 =
      333333 / 1000000 := by
  norm_num

/-- The raw weight-one miss has a strict exact margin below one third. -/
theorem raw_miss_below_third :
    (333333 : ℚ) / 1000000 < 1 / 3 := by
  norm_num

/-- The exact raw margin is one part in three million. -/
theorem raw_margin_identity :
    (1 : ℚ) / 3 - 333333 / 1000000 = 1 / 3000000 := by
  norm_num

/-- The weight-two raw miss is already smaller than the weight-one value. -/
theorem weight_two_below_weight_one :
    (((1 : ℚ) + (277 / 500) ^ 2) *
        ((1 : ℚ) + (71 / 500) ^ 2)) / 4 <
      333333 / 1000000 := by
  norm_num

/-- The simple odd-weight cubic envelope lies below the exact worst-case
weight-one miss. -/
theorem odd_cubic_envelope_below_weight_one :
    ((1 : ℚ) + (277 / 500) ^ 3) / 4 <
      333333 / 1000000 := by
  norm_num

/-- Conditioning each row on an event of probability at least
`3999999/4000000` preserves a strict pointwise error margin below one third. -/
theorem conditioned_miss_below_third :
    ((333333 : ℚ) / 1000000) /
        (((3999999 : ℚ) / 4000000) ^ 2) < 1 / 3 := by
  norm_num

/-- The two linear support numerators add to the scaled coefficient `397/500`. -/
theorem support_numerators_add (d : ℤ) :
    223 * d + 571 * d = 2 * 397 * d := by
  ring

/-- Exact scaled padding obstruction. If a Rep circuit has lower bound
`2*N+g`, while the construction upper-bounds five hundred times its size by a
source circuit plus the `397/500` shell, then the source already pays the
remaining `603/500` ambient coefficient. -/
theorem rep_lower_bound_forces_source_lower_bound
    {N m g rep source err : ℤ}
    (hlower : 2 * N + g ≤ rep)
    (hupper :
      500 * rep ≤
        500 * source + 397 * (N - m) + 1000 * m + err) :
    603 * N + 500 * g ≤ 500 * source + 603 * m + err := by
  linarith

/-- Equivalent regrouping of the shell numerator. -/
theorem shell_regroup (N m : ℤ) :
    397 * (N - m) + 1000 * m = 397 * N + 603 * m := by
  ring

#print axioms support_density_identity
#print axioms weight_one_raw_miss
#print axioms raw_miss_below_third
#print axioms raw_margin_identity
#print axioms weight_two_below_weight_one
#print axioms odd_cubic_envelope_below_weight_one
#print axioms conditioned_miss_below_third
#print axioms support_numerators_add
#print axioms rep_lower_bound_forces_source_lower_bound
#print axioms shell_regroup

end B2Round42PNP
end MillenniumBraid
