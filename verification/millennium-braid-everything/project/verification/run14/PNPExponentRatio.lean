import Mathlib

namespace MillenniumRun14

/-- A strict exponent gap yields the basic monomial domination used by the
uniform tagged-union hardwiring argument. -/
theorem pnp_exponent_gap_monomial
    (n d v h : ℕ)
    (hn : 1 ≤ n)
    (hexp : d * v < h) :
    n ^ (d * v) ≤ n ^ h := by
  exact Nat.pow_le_pow_right hn (Nat.le_of_lt hexp)

/-- Finite algebraic core of the CLY padding-ratio conservation obstruction.
If padding converts original verifier exponent `a` into padded exponent `v`
(`a ≤ θ*v`) while a padded hardness exponent `h` must fit inside original
replacement budget `δ` (`θ*h ≤ δ`), then the hardness/verifier ratio cannot
outrun the fixed budget ratio: `a*h ≤ δ*v`.  This is division-free so it also
covers zero parameters without side conditions. -/
theorem pnp_padding_ratio_conservation
    (a h δ θ v : ℕ)
    (hver : a ≤ θ * v)
    (hbudget : θ * h ≤ δ) :
    a * h ≤ δ * v := by
  calc
    a * h ≤ (θ * v) * h := Nat.mul_le_mul_right h hver
    _ = (θ * h) * v := by ac_rfl
    _ ≤ δ * v := Nat.mul_le_mul_right v hbudget

end MillenniumRun14
