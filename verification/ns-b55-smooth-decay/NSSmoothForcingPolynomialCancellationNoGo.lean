import Mathlib

/-!
# Polynomial cancellation versus superpolynomial decay

This file contains only the scalar finite/eventual logic used after the human
Fourier-analysis theorem for smooth periodic forcing.

No Navier--Stokes equation, Fourier estimate, or Clay conclusion is assumed.
-/

namespace NSSmoothForcingPolynomialCancellationNoGo

/-- At one scale, a polynomial lower bound for `a`, a one-extra-power upper
bound for `b`, and `C < c*N` are incompatible with exact cancellation. -/
theorem polynomial_lower_vs_next_power_upper
    {N c C a b : ℝ} {r : ℕ}
    (hN : 0 ≤ N)
    (hpoly : c ≤ N ^ r * |a|)
    (hrapid : N ^ (r + 1) * |b| ≤ C)
    (hlarge : C < c * N)
    (hcancel : a + b = 0) :
    False := by
  have hb : b = -a := by linarith
  have habs : |b| = |a| := by simp [hb]
  have hmul := mul_le_mul_of_nonneg_left hpoly hN
  have hscaled : c * N ≤ N ^ (r + 1) * |a| := by
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hrapid' : N ^ (r + 1) * |a| ≤ C := by
    simpa [habs] using hrapid
  exact (not_lt_of_ge (hscaled.trans hrapid')) hlarge

/-- Eventual form: once all three scale inequalities hold eventually, exact
cancellation is eventually impossible. -/
theorem eventual_polynomial_cancellation_impossible
    {N a b : ℕ → ℝ} {c C : ℝ} {r : ℕ}
    (hN : ∀ n, 0 ≤ N n)
    (hpoly : ∀ᶠ n in Filter.atTop, c ≤ (N n) ^ r * |a n|)
    (hrapid : ∀ᶠ n in Filter.atTop,
      (N n) ^ (r + 1) * |b n| ≤ C)
    (hlarge : ∀ᶠ n in Filter.atTop, C < c * N n) :
    ∀ᶠ n in Filter.atTop, a n + b n ≠ 0 := by
  filter_upwards [hpoly, hrapid, hlarge] with n hp hr hl
  intro hcancel
  exact polynomial_lower_vs_next_power_upper (hN n) hp hr hl hcancel

#print axioms polynomial_lower_vs_next_power_upper
#print axioms eventual_polynomial_cancellation_impossible

end NSSmoothForcingPolynomialCancellationNoGo
