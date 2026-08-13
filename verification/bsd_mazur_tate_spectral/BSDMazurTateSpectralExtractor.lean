import Mathlib

namespace BSDMazurTateSpectralExtractor

/-- The abstract two-layer spectral filter. If a finite-layer invariant is a
universal term plus a stationary arithmetic term, and the universal term has
an affine p^2 recurrence, then the filter recovers the stationary term. -/
theorem recover_stationary_mode
    {p M M₂ q q₂ c lam : ℤ}
    (hM : M = q + lam)
    (hM₂ : M₂ = q₂ + lam)
    (hq : q₂ = p ^ 2 * q + c) :
    p ^ 2 * M - M₂ + c = (p ^ 2 - 1) * lam := by
  rw [hM, hM₂, hq]
  ring

/-- Three same-parity layers satisfy the exact two-mode recurrence. -/
theorem two_mode_recurrence
    {p M₀ M₁ M₂ q₀ q₁ q₂ c lam : ℤ}
    (hM₀ : M₀ = q₀ + lam)
    (hM₁ : M₁ = q₁ + lam)
    (hM₂ : M₂ = q₂ + lam)
    (hq₁ : q₁ = p ^ 2 * q₀ + c)
    (hq₂ : q₂ = p ^ 2 * q₁ + c) :
    M₂ - (p ^ 2 + 1) * M₁ + p ^ 2 * M₀ = 0 := by
  rw [hM₀, hM₁, hM₂, hq₂, hq₁]
  ring

/-- The extracted numerator is nonnegative when it equals a nonnegative
Iwasawa lambda-invariant times p^2-1 and p is at least 2. -/
theorem extraction_numerator_nonnegative
    {p numerator lam : ℤ}
    (hp : 2 ≤ p)
    (hlam : 0 ≤ lam)
    (h : numerator = (p ^ 2 - 1) * lam) :
    0 ≤ numerator := by
  rw [h]
  have hpm1 : 0 ≤ p - 1 := by omega
  have hpp1 : 0 ≤ p + 1 := by omega
  have hpnon : 0 ≤ p ^ 2 - 1 := by
    calc
      0 ≤ (p - 1) * (p + 1) := mul_nonneg hpm1 hpp1
      _ = p ^ 2 - 1 := by ring
  exact mul_nonneg hpnon hlam

/-- Exact divisibility certificate for the spectral numerator. -/
theorem extraction_numerator_divisible
    {p numerator lam : ℤ}
    (h : numerator = (p ^ 2 - 1) * lam) :
    ∃ k : ℤ, numerator = (p ^ 2 - 1) * k := by
  exact ⟨lam, h⟩

/-- Four finite layers recover two stationary signed coordinates independently. -/
theorem recover_signed_pair
    {p Me Me₂ Mo Mo₂ ce co sharp flat : ℤ}
    (he : p ^ 2 * Me - Me₂ + ce = (p ^ 2 - 1) * sharp)
    (ho : p ^ 2 * Mo - Mo₂ + co = (p ^ 2 - 1) * flat) :
    (p ^ 2 * Me - Me₂ + ce = (p ^ 2 - 1) * sharp) ∧
      (p ^ 2 * Mo - Mo₂ + co = (p ^ 2 - 1) * flat) := by
  exact ⟨he, ho⟩

/-- A finite window of exact recurrences cannot certify that the asymptotic
stable range has begun. For every tested depth `N`, this explicit sequence
satisfies the recurrence at every index `n ≤ N` and fails at the next index. -/
def fakeStableSequence (N n : ℕ) : ℤ :=
  if n = N + 5 then 1 else 0

theorem fakeStableSequence_prefix_recurrence
    (N n : ℕ) (p : ℤ) (hn : n ≤ N) :
    fakeStableSequence N (n + 4) -
        (p ^ 2 + 1) * fakeStableSequence N (n + 2) +
        p ^ 2 * fakeStableSequence N n = 0 := by
  have h0 : n ≠ N + 5 := by omega
  have h2 : n + 2 ≠ N + 5 := by omega
  have h4 : n + 4 ≠ N + 5 := by omega
  simp [fakeStableSequence, h0, h2, h4]

theorem fakeStableSequence_next_recurrence_fails
    (N : ℕ) (p : ℤ) :
    fakeStableSequence N (N + 5) -
        (p ^ 2 + 1) * fakeStableSequence N (N + 3) +
        p ^ 2 * fakeStableSequence N (N + 1) ≠ 0 := by
  have h1 : N + 1 ≠ N + 5 := by omega
  have h3 : N + 3 ≠ N + 5 := by omega
  simp [fakeStableSequence, h1, h3]

#print axioms recover_stationary_mode
#print axioms two_mode_recurrence
#print axioms extraction_numerator_nonnegative
#print axioms extraction_numerator_divisible
#print axioms recover_signed_pair
#print axioms fakeStableSequence_prefix_recurrence
#print axioms fakeStableSequence_next_recurrence_fails

end BSDMazurTateSpectralExtractor
