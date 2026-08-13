import Mathlib

namespace MillenniumRun14

/-- Padding to exponent `k` and then paying any polynomial exponent `d ≥ 1`
produces exponent `d*k`, never smaller than the original `k`. -/
theorem pnp_naive_padding_does_not_improve_exponent
    (d k : ℕ)
    (hd : 1 ≤ d) :
    k ≤ d * k := by
  simpa [one_mul] using Nat.mul_le_mul_right k hd

end MillenniumRun14
