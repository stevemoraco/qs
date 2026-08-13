import Mathlib

namespace RHCausalGapReserveFinite

/-- Exact scalar value of the causal gap profile at an interior critical point.
Here `u = sqrt x` and the critical relation is
`B - 4/3 = (2/3) u^3`. -/
theorem interior_critical_value
    {u A B : ℝ}
    (_hu : u ≠ 0)
    (hcrit : B - 4 / 3 = (2 / 3) * u ^ 3) :
    (4 / 3) * u - A + (B - 4 / 3) / u ^ 2 = 2 * u - A := by
  rw [hcrit]
  field_simp [_hu]
  ring

/-- Exact cubic arrival ledger.  The cubic coordinate moves from `v` to `u`,
its cube increment is `(3/2) p a`, and the linear prime prefix pays `a`. -/
theorem cubic_reserve_step
    {u v p a A₀ A₁ : ℝ}
    (hden : u ^ 2 + u * v + v ^ 2 ≠ 0)
    (hcube : u ^ 3 - v ^ 3 = (3 / 2) * p * a)
    (hA : A₁ = A₀ + a) :
    (2 * u - A₁) - (2 * v - A₀) =
      a * (3 * p / (u ^ 2 + u * v + v ^ 2) - 1) := by
  rw [hA]
  have hfactor : (u - v) * (u ^ 2 + u * v + v ^ 2) = (3 / 2) * p * a := by
    calc
      (u - v) * (u ^ 2 + u * v + v ^ 2) = u ^ 3 - v ^ 3 := by ring
      _ = (3 / 2) * p * a := hcube
  have hdiff : u - v = ((3 / 2) * p * a) / (u ^ 2 + u * v + v ^ 2) := by
    exact (eq_div_iff hden).2 hfactor
  calc
    (2 * u - (A₀ + a)) - (2 * v - A₀) = 2 * (u - v) - a := by ring
    _ = 2 * (((3 / 2) * p * a) / (u ^ 2 + u * v + v ^ 2)) - a := by rw [hdiff]
    _ = a * (3 * p / (u ^ 2 + u * v + v ^ 2) - 1) := by
      field_simp [hden]
      ring

/-- A positive point and integral lower bound for the inverse Volterra
expression produce an explicit scalar lower bound.  This is only the final
ordered-algebra ledger, not the analytic integral theorem. -/
theorem inverse_lower_bound_ledger
    {h i B r q C : ℝ}
    (hr : 0 < r)
    (hh : -B ≤ h)
    (hi : -2 * B * r + C ≤ i) :
    -B - q + C / (4 * r) + 1 / r ≤
      h / 2 + i / (4 * r) - q + 1 / r := by
  have hr4 : 0 < 4 * r := by positivity
  have hi' : (-2 * B * r + C) / (4 * r) ≤ i / (4 * r) :=
    div_le_div_of_nonneg_right hi (le_of_lt hr4)
  have hh' : -B / 2 ≤ h / 2 := by linarith
  have hid : (-2 * B * r + C) / (4 * r) = -B / 2 + C / (4 * r) := by
    field_simp [ne_of_gt hr]
    ring
  rw [hid] at hi'
  linarith

/-- Exact factorization of the derivative numerator of the frozen causal gap
profile after clearing the positive denominator. -/
theorem causal_derivative_numerator
    {x K : ℝ} :
    (2 / 3) * x ^ (3 : ℕ) - (2 / 3) * K =
      (2 / 3) * (x ^ 3 - K) := by
  ring

/-- The clamped minimum is automatically no smaller than the unconstrained
interior critical value when the profile is globally minimized there.  This
finite lemma records only the order step consumed after the analytic shape
proof has been supplied. -/
theorem constrained_min_ge_global
    {global constrained : ℝ}
    (h : global ≤ constrained) :
    constrained ≥ global := h

#print axioms interior_critical_value
#print axioms cubic_reserve_step
#print axioms inverse_lower_bound_ledger
#print axioms causal_derivative_numerator
#print axioms constrained_min_ge_global

end RHCausalGapReserveFinite
