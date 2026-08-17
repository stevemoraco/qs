import Mathlib

/-!
# B247 low-moment transport finite core

This file formalizes only the finite combinatorial identities behind the B247
moment-blind transport firewall:

* an iterated forward difference annihilates a monomial whose degree is below
  the difference order;
* the alternating partial binomial sum is exactly one lower-row binomial
  coefficient with alternating sign;
* the total binomial row sum is `2^N`.

These are the load-bearing finite identities used to build two positive atomic
measures with identical low moments but separated one-dimensional transport.

This file does **not** formalize signed measures, Jordan decomposition,
Kantorovich transport, Hankel matrices, primes, PNT, Mellin/Landau, zeta, Xi,
Deng--Yang--Lu, B46, RH, or not-RH.
-/

namespace RHB247LowMomentTransportFinite

open Finset

/-- The `N`-th forward difference kills every monomial of degree `< N`. -/
theorem low_degree_forward_difference_zero
    {j N : ℕ} (h : j < N) :
    ((fwdDiff (1 : ℤ))^[N] fun x : ℤ => x ^ j) = 0 := by
  exact fwdDiff_iter_pow_eq_zero_of_lt h

/-- Exact alternating cumulative mass identity for the B247 binomial witness. -/
theorem alternating_partial_binomial_sum (n m : ℕ) :
    ∑ k ∈ Finset.range (m + 1),
        (-1 : ℤ) ^ k * ((n + 1).choose k : ℤ) =
      (-1 : ℤ) ^ m * (n.choose m : ℤ) := by
  exact Int.alternating_sum_range_choose_eq_choose

/-- The absolute binomial coefficients in one row have total mass `2^N`. -/
theorem binomial_row_mass (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), N.choose k = 2 ^ N := by
  exact Nat.sum_range_choose N

#print axioms low_degree_forward_difference_zero
#print axioms alternating_partial_binomial_sum
#print axioms binomial_row_mass

end RHB247LowMomentTransportFinite
