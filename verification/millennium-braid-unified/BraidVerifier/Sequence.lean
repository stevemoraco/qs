import Mathlib

namespace BraidVerifier.Sequence

theorem two_mode
    {p M₀ M₁ M₂ q₀ q₁ q₂ c lam : ℤ}
    (hM₀ : M₀ = q₀ + lam)
    (hM₁ : M₁ = q₁ + lam)
    (hM₂ : M₂ = q₂ + lam)
    (hq₁ : q₁ = p ^ 2 * q₀ + c)
    (hq₂ : q₂ = p ^ 2 * q₁ + c) :
    M₂ - (p ^ 2 + 1) * M₁ + p ^ 2 * M₀ = 0 := by
  rw [hM₀, hM₁, hM₂, hq₂, hq₁]
  ring

end BraidVerifier.Sequence
