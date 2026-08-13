import Mathlib

/-!
# Bounded-depth Sha indistinguishability arithmetic firewall

This file formalizes only exponent and cardinality arithmetic behind the
round-42 BSD obstruction. It does not formalize finite abelian groups,
`Q_p/Z_p`, pairings into `Q/Z`, Selmer groups, elliptic curves, Sha, or BSD.
-/

namespace MillenniumBraid
namespace B2Round42BSD

/-- Every symplectic layer of rank two has square cardinality `p^(2*n)`. -/
theorem layer_cardinality_is_square (p n : ℕ) :
    p ^ (2 * n) = (p ^ n) ^ 2 := by
  rw [pow_two, ← pow_add]
  congr 1
  omega

/-- At ambient exponent `2*N`, elements killed by `p^n` are represented with
scale exponent `2*N-n`; pairing two such elements leaves an integral factor
when `n≤N`. -/
theorem shallow_pairing_exponent_identity
    {N n : ℕ} (hn : n ≤ N) :
    2 * (2 * N - n) = 2 * N + 2 * (N - n) := by
  omega

/-- Corresponding exact power factorization. -/
theorem shallow_pairing_power_factorization
    (p : ℕ) {N n : ℕ} (hn : n ≤ N) :
    p ^ (2 * (2 * N - n)) =
      p ^ (2 * N) * p ^ (2 * (N - n)) := by
  rw [shallow_pairing_exponent_identity hn, pow_add]

/-- The shallow numerator is divisible by the full pairing denominator. -/
theorem shallow_pairing_numerator_divisible
    (p : ℕ) {N n : ℕ} (hn : n ≤ N) :
    p ^ (2 * N) ∣ p ^ (2 * (2 * N - n)) := by
  refine ⟨p ^ (2 * (N - n)), ?_⟩
  exact (shallow_pairing_power_factorization p hn).symm

/-- A layer inspected no deeper than `N` lies below the ambient exponent
`2*N`, so truncating the finite model at `2*N` does not alter that layer. -/
theorem inspected_layer_below_ambient
    {N n : ℕ} (hn : n ≤ N) :
    n ≤ 2 * N := by
  omega

/-- Arithmetic shadow of identical finite and divisible layer sizes through
inspection depth `N`. -/
theorem bounded_layers_same_cardinality
    (p : ℕ) {N n : ℕ} (_hn : n ≤ N) :
    p ^ (2 * n) = p ^ (2 * n) := by
  rfl

/-- No finite maximum inspection depth can exhaust the possible ambient
exponent: `2*N` is always strictly larger than `N` when `N>0`. -/
theorem ambient_depth_escapes_inspection
    {N : ℕ} (hN : 0 < N) :
    N < 2 * N := by
  omega

#print axioms layer_cardinality_is_square
#print axioms shallow_pairing_exponent_identity
#print axioms shallow_pairing_power_factorization
#print axioms shallow_pairing_numerator_divisible
#print axioms inspected_layer_below_ambient
#print axioms bounded_layers_same_cardinality
#print axioms ambient_depth_escapes_inspection

end B2Round42BSD
end MillenniumBraid
