import Mathlib

namespace RHCausalGapReserveFinite

/-!
Finite scalar algebra for the causal ordinary-prime RH statistic.

Scope firewall: this file does not define primes, Chebyshev theta, Stieltjes
integrals, Johnston's theorem, zeta zeros, or RH.  It formalizes only the
algebraic identities used after those analytic objects have been constructed.
-/

/-- If `R = 2s-A` and
`H = (4/3)(s-1/x)-A+B/x`, then the causal lag has the exact form
`x(R-H) = (2/3)xs+4/3-B`. -/
theorem lag_identity
    {x s A B R H : ℝ}
    (hx : x ≠ 0)
    (hR : R = 2 * s - A)
    (hH : H = (4 / 3 : ℝ) * (s - 1 / x) - A + B / x) :
    x * (R - H) = (2 / 3 : ℝ) * x * s + 4 / 3 - B := by
  rw [hR, hH]
  field_simp [hx]
  ring

/-- The algebraic factorization controlling the unique critical point on a
prime gap. -/
theorem difference_of_cubes
    (y₀ y₁ : ℝ) :
    y₁ ^ 3 - y₀ ^ 3 =
      (y₁ - y₀) * (y₁ ^ 2 + y₁ * y₀ + y₀ ^ 2) := by
  ring

/-- At an interior critical point, the cubic equation
`2y^3+4=3B` simplifies the causal statistic exactly to `2y-A`. -/
theorem critical_value
    {y A B H : ℝ}
    (hy : y ≠ 0)
    (hB : 2 * y ^ 3 + 4 = 3 * B)
    (hH : H = (4 / 3 : ℝ) * (y - 1 / y ^ 2) - A + B / y ^ 2) :
    H = 2 * y - A := by
  have hB' : B = (2 * y ^ 3 + 4) / 3 := by
    linarith
  rw [hH, hB']
  field_simp [hy]
  ring

/-- Exact cube-root reserve increment.  The hypotheses expose every bridge:
`B` receives one weighted claim `r*a`, `A` receives `a/r`, and the two cubic
coordinates solve `2y^3+4=3B`. -/
theorem cube_root_reserve_increment
    {r a A₀ A₁ B₀ B₁ y₀ y₁ G₀ G₁ : ℝ}
    (hr : r ≠ 0)
    (hden : y₁ ^ 2 + y₁ * y₀ + y₀ ^ 2 ≠ 0)
    (hBstep : B₁ = B₀ + r * a)
    (hy₀ : 2 * y₀ ^ 3 + 4 = 3 * B₀)
    (hy₁ : 2 * y₁ ^ 3 + 4 = 3 * B₁)
    (hAstep : A₁ = A₀ + a / r)
    (hG₀ : G₀ = 2 * y₀ - A₀)
    (hG₁ : G₁ = 2 * y₁ - A₁) :
    G₁ - G₀ =
      a * (3 * r / (y₁ ^ 2 + y₁ * y₀ + y₀ ^ 2) - 1 / r) := by
  let d : ℝ := y₁ ^ 2 + y₁ * y₀ + y₀ ^ 2
  have hd : d ≠ 0 := by
    simpa [d] using hden
  have hcubic : 2 * (y₁ ^ 3 - y₀ ^ 3) = 3 * r * a := by
    rw [hBstep] at hy₁
    linarith
  have hfactor : y₁ ^ 3 - y₀ ^ 3 = (y₁ - y₀) * d := by
    simp only [d]
    ring
  have hcore : 2 * (y₁ - y₀) * d = 3 * r * a := by
    rw [← hfactor]
    exact hcubic
  rw [hG₁, hG₀, hAstep]
  simp only [d] at hd hcore ⊢
  field_simp [hr, hd]
  nlinarith

/-- The sign comparison behind a refill: if the denominator is positive and
smaller than `3 r^2`, then the cube-root increment coefficient is positive. -/
theorem refill_coefficient_positive
    {r d : ℝ}
    (hr : 0 < r)
    (hd : 0 < d)
    (hcmp : d < 3 * r ^ 2) :
    0 < 3 * r / d - 1 / r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hd0 : d ≠ 0 := ne_of_gt hd
  field_simp [hr0, hd0]
  nlinarith

/-- Dually, if the cubic denominator is larger than `3 r^2`, the local
reserve coefficient is negative. -/
theorem drain_coefficient_negative
    {r d : ℝ}
    (hr : 0 < r)
    (hd : 0 < d)
    (hcmp : 3 * r ^ 2 < d) :
    3 * r / d - 1 / r < 0 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hd0 : d ≠ 0 := ne_of_gt hd
  field_simp [hr0, hd0]
  nlinarith

#print axioms lag_identity
#print axioms difference_of_cubes
#print axioms critical_value
#print axioms cube_root_reserve_increment
#print axioms refill_coefficient_positive
#print axioms drain_coefficient_negative

end RHCausalGapReserveFinite
