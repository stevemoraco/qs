import Mathlib

/-!
# RH B115 near-trace Schatten finite core

Finite real/rational algebra only.  This file records the load-bearing exponent
ledger and hostile fixed-moment witnesses behind the B115 reduction.

It does not formalize primes, zeta, B109B, rearrangement theory, Schatten
functional calculus, generalized eigenvalues, asymptotics, or the Riemann
hypothesis.
-/

namespace RHB115NearTraceSchattenFinite

/-- For the canonical near-trace exponent `p=(k+1)/k`, the Hölder conjugate is
exactly `q=k+1`. -/
theorem canonical_conjugate_exponent_ledger
    {k : ℝ} (hk : k ≠ 0) :
    let p := (k + 1) / k
    (p - 1 = 1 / k) ∧
    (p / (p - 1) = k + 1) := by
  dsimp
  constructor
  · field_simp [hk]
    ring
  · have hk1 : (1 / k : ℝ) ≠ 0 := one_div_ne_zero hk
    rw [show (k + 1) / k - 1 = 1 / k by
      field_simp [hk]
      ring]
    field_simp [hk, hk1]
    ring

/-- The dimension-loss exponent for `p=(k+1)/k` is `1/(k+1)`. -/
theorem canonical_dimension_loss_exponent
    {k : ℝ} (hk : k ≠ 0) (hk1 : k + 1 ≠ 0) :
    let p := (k + 1) / k
    1 - 1 / p = 1 / (k + 1) := by
  dsimp
  field_simp [hk, hk1]
  ring

/-- Polynomial shadow of the Fenchel optimizer.  If the primal depth is `y^k`,
then the canonical dual expression at `y` has the exact optimizer value
`k*y^(k+1)`. -/
theorem polynomial_dual_optimizer_shadow
    (k : ℕ) (y : ℝ) :
    (((k + 1 : ℕ) : ℝ) * y * (y ^ k) - y ^ (k + 1))
      = (k : ℝ) * y ^ (k + 1) := by
  rw [pow_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- The quadratic member of the Fenchel family: the penalized linear form is
always bounded by the positive quadratic depth. -/
theorem quadratic_fenchel_upper
    (x y : ℝ) :
    2 * y * x - y ^ 2 ≤ x ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

/-- The quadratic optimizer attains equality at `y=x`. -/
theorem quadratic_fenchel_attains
    (x : ℝ) :
    2 * x * x - x ^ 2 = x ^ 2 := by
  ring

/-- Hostile fixed-exponent witness: a block of `m^2` equal depths `1/m` has
unit quadratic moment but weak/total depth `m`.  Thus a fixed `p=2` moment can
stay bounded while the weak-L1 scale grows arbitrarily. -/
theorem fixed_quadratic_moment_blindness
    {m : ℝ} (hm : m ≠ 0) :
    (m ^ 2) * (1 / m) ^ 2 = 1 ∧
    (m ^ 2) * (1 / m) = m := by
  constructor
  · field_simp [hm]
  · field_simp [hm]

/-- In the same hostile family, every `m>1` gives strictly larger weak depth
than its unit quadratic moment. -/
theorem fixed_quadratic_moment_loses_power
    {m : ℝ} (hm : 1 < m) :
    (1 : ℝ) < (m ^ 2) * (1 / m) := by
  have hm0 : m ≠ 0 := ne_of_gt (lt_trans (by norm_num) hm)
  rw [(fixed_quadratic_moment_blindness hm0).2]
  exact hm

/-- Scalar congruence-depth firewall for a quadratic near-trace observable:
rescaling a negative scalar by `R^2` preserves its sign but multiplies squared
negative depth by `R^4`. -/
theorem congruence_rescales_quadratic_depth
    (R : ℝ) :
    ((R ^ 2) ^ 2) = R ^ 4 := by
  ring

#print axioms canonical_conjugate_exponent_ledger
#print axioms canonical_dimension_loss_exponent
#print axioms polynomial_dual_optimizer_shadow
#print axioms quadratic_fenchel_upper
#print axioms quadratic_fenchel_attains
#print axioms fixed_quadratic_moment_blindness
#print axioms fixed_quadratic_moment_loses_power
#print axioms congruence_rescales_quadratic_depth

end RHB115NearTraceSchattenFinite
