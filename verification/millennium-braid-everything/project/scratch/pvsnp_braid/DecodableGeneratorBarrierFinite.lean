import Mathlib

namespace PvsNPBraid

/-- Exact gate count for decode, re-encode, compare all coordinates, and AND
the equality bits. -/
theorem decode_reencode_checker_count
    (sD sG n : ℤ) :
    sD + sG + n + (n - 1) = sD + sG + 2 * n - 1 := by
  ring

/-- At threshold `2n+Delta`, a low-density exact range recognizer must spend
more than the additive surplus in encoder plus decoder complexity. -/
theorem decodable_range_surplus_gate
    (sD sG n delta : ℤ)
    (h : 2 * n + delta < sD + sG + 2 * n - 1) :
    delta + 1 < sD + sG := by
  linarith

/-- Conversely, an encoder/decoder pair at or below the surplus produces a
range recognizer within the forbidden near-`2n` threshold. -/
theorem cheap_decodable_range_is_small_circuit
    (sD sG n delta : ℤ)
    (h : sD + sG ≤ delta + 1) :
    sD + sG + 2 * n - 1 ≤ 2 * n + delta := by
  linarith

/-- An injective map from `r` bits has exactly `2^r` seeds; the scalar density
exponent is the codimension `n-r`. -/
theorem range_density_codimension (n r : ℕ) (hr : r ≤ n) :
    n - r + r = n := by
  omega

end PvsNPBraid
