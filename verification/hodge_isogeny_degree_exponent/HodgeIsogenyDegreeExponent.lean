import Mathlib

namespace Millennium.Hodge.IsogenyDegreeExponent

/-- BANKER: the standard multiplication-map degree exponent `2g` becomes
`4n` when the abelian variety has dimension `g = 2n`. -/
theorem banker_integer_scalar_degree_in_weil_dimension
    (m g n : ℕ) (hg : g = 2 * n) :
    m ^ (2 * g) = m ^ (4 * n) := by
  subst g
  apply congrArg (fun e : ℕ => m ^ e)
  omega

/-- CRITIC: in dimension four (`n = 2`), the integer scalar `2` has the
standard degree `2^8 = 256`, not the quadratic norm value `2^2 = 4`. -/
theorem critic_quadratic_norm_is_not_isogeny_degree_in_dimension_four :
    (2 : ℕ) ^ 8 ≠ 2 ^ 2 := by
  norm_num

/-- CLEANER: for an integer inside an imaginary quadratic field, whose field
norm is `m^2`, the corrected dimension-sensitive degree is its `2n`-th power. -/
theorem cleaner_norm_power_recovers_integer_scalar_degree
    (m n : ℕ) :
    (m ^ 2) ^ (2 * n) = m ^ (4 * n) := by
  rw [← pow_mul]
  apply congrArg (fun e : ℕ => m ^ e)
  omega

#print axioms banker_integer_scalar_degree_in_weil_dimension
#print axioms critic_quadratic_norm_is_not_isogeny_degree_in_dimension_four
#print axioms cleaner_norm_power_recovers_integer_scalar_degree

end Millennium.Hodge.IsogenyDegreeExponent
