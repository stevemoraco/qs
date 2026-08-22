import Mathlib

namespace BraidVerifier.Count

theorem ledger
    (N k b r d : ℤ) (hN : N = k * b) :
    (k - 1) * (b - 1) + b * (k - 1) + (2 * k - 2 - 2 * r) + d =
      2 * N + k - 2 * b - 1 - 2 * r + d := by
  rw [hN]
  ring

end BraidVerifier.Count
