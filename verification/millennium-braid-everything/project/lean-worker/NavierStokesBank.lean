import Mathlib

namespace NavierStokesBank

/-- Young's inequality with exponents `3` and `3/2`, polynomialized by
writing the second factor as a square. This is the scalar exponent step
behind the rate-free truncation source term. -/
theorem young_three_threeHalves (x z : ℝ) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    x * z ^ 2 ≤ x ^ 3 / 3 + 2 * z ^ 3 / 3 := by
  have hsum : 0 ≤ x + 2 * z := by positivity
  have hprod : 0 ≤ (x - z) ^ 2 * (x + 2 * z) :=
    mul_nonneg (sq_nonneg (x - z)) hsum
  nlinarith

/-- Two independent half-error estimates close one endpoint smallness
budget. -/
theorem two_half_errors {a b ε : ℝ}
    (ha : a ≤ ε / 2) (hb : b ≤ ε / 2) : a + b ≤ ε := by
  linarith

/-- The scalar steady-state banking step for a damped inequality. -/
theorem steady_state_bank {E source damping : ℝ}
    (hdamping : 0 < damping)
    (h : damping * E ≤ source) :
    E ≤ source / damping := by
  apply (le_div_iff₀ hdamping).2
  simpa [mul_comm] using h

/-- Chebyshev algebra for a truncation at height `λ`. -/
theorem truncation_chebyshev {d E λ : ℝ}
    (hλ : 0 < λ)
    (h : d * λ ^ 2 ≤ E) :
    d ≤ E / λ ^ 2 := by
  have hλ2 : 0 < λ ^ 2 := pow_pos hλ 2
  exact (le_div_iff₀ hλ2).2 h

/-- Algebraic balance for the intermediate commutator scale
`L² = R r₀ / 4`. -/
theorem intermediate_scale_balance
    {R r₀ L : ℝ}
    (hR : 0 < R) (hr₀ : 0 < r₀)
    (hscale : L ^ 2 = R * r₀ / 4) :
    (R / L) ^ 2 = 4 * R / r₀ := by
  rw [div_pow, hscale]
  field_simp [ne_of_gt hR, ne_of_gt hr₀]
  <;> ring

/-- Dividing a source of size `λ^(3/2) a^(3/2)` by critical damping of
size `λ` leaves the `λ^(1/2) a^(3/2)` energy scale. The fractional powers
are abstracted as a common nonnegative factor `q`. -/
theorem critical_damping_exponent_bank
    {λ q c E : ℝ}
    (hλ : 0 < λ) (hc : 0 < c)
    (h : c * λ * E ≤ λ * q) :
    E ≤ q / c := by
  have hcl : 0 < c * λ := mul_pos hc hλ
  have h' : (c * λ) * E ≤ λ * q := by
    simpa [mul_assoc] using h
  have hdiv := (le_div_iff₀ hcl).2 h'
  calc
    E ≤ (λ * q) / (c * λ) := hdiv
    _ = q / c := by field_simp [ne_of_gt hλ, ne_of_gt hc] <;> ring

/-- A local endpoint estimate obtained by combining a critical tail with
a bounded low-amplitude piece. -/
theorem local_endpoint_split
    {tail K volumeRoot ε : ℝ}
    (htail : tail ≤ ε / 2)
    (hlow : K * volumeRoot ≤ ε / 2) :
    tail + K * volumeRoot ≤ ε := by
  linarith

/-- Abstract zero-data Leray-Hopf rigidity. A nonnegative energy plus a
strictly viscous nonnegative dissipation cannot be nonpositive unless both
terms vanish. -/
theorem zero_data_energy_rigidity
    {E D ν : ℝ}
    (hE : 0 ≤ E) (hD : 0 ≤ D) (hν : 0 < ν)
    (henergy : E + ν * D ≤ 0) :
    E = 0 ∧ D = 0 := by
  have hνD : 0 ≤ ν * D := mul_nonneg (le_of_lt hν) hD
  have hsum : 0 ≤ E + ν * D := add_nonneg hE hνD
  have hsum0 : E + ν * D = 0 := le_antisymm henergy hsum
  have hE0 : E = 0 := by nlinarith
  have hprod0 : ν * D = 0 := by nlinarith
  have hνne : ν ≠ 0 := ne_of_gt hν
  exact ⟨hE0, (mul_eq_zero.mp hprod0).resolve_left hνne⟩

/-- Abstract stationary Leray-Hopf rigidity. Equal endpoint energies leave
no room for positive viscous dissipation on a nontrivial time interval. -/
theorem stationary_energy_rigidity
    {E D ν s t : ℝ}
    (hD : 0 ≤ D) (hν : 0 < ν) (hst : s < t)
    (henergy : E + ν * (t - s) * D ≤ E) :
    D = 0 := by
  have hcoef : 0 < ν * (t - s) := mul_pos hν (sub_pos.mpr hst)
  have hprod_le : ν * (t - s) * D ≤ 0 := by linarith
  have hprod_nonneg : 0 ≤ ν * (t - s) * D :=
    mul_nonneg (le_of_lt hcoef) hD
  have hprod0 : ν * (t - s) * D = 0 :=
    le_antisymm hprod_le hprod_nonneg
  have hcoef_ne : ν * (t - s) ≠ 0 := ne_of_gt hcoef
  exact (mul_eq_zero.mp hprod0).resolve_left hcoef_ne

/-- Algebraic core of the critical-thickness bridge. Here `q` is the
cube-root of witness volume. A weak-Lorentz witness `a ≤ μ q²` forces
stretching work at least `a λ² q`. -/
theorem critical_witness_work_lower
    {μ q a λ work : ℝ}
    (hq : 0 ≤ q)
    (hweak : a ≤ μ * q ^ 2)
    (hwork : μ * λ ^ 2 * q ^ 3 ≤ work) :
    a * λ ^ 2 * q ≤ work := by
  have hfactor : 0 ≤ λ ^ 2 * q :=
    mul_nonneg (sq_nonneg λ) hq
  have hmul := mul_le_mul_of_nonneg_right hweak hfactor
  calc
    a * λ ^ 2 * q = a * (λ ^ 2 * q) := by ring
    _ ≤ (μ * q ^ 2) * (λ ^ 2 * q) := hmul
    _ = μ * λ ^ 2 * q ^ 3 := by ring
    _ ≤ work := hwork

/-- Exact parabolic scale normalization. If vorticity amplitude `K` and
length `r` obey `K r² = 1`, then a critical packet persisting for time
`r²` contributes normalized work exactly `a`. -/
theorem parabolic_work_normalization
    {a K r : ℝ}
    (hscale : K * r ^ 2 = 1) :
    r * (a * K ^ 2 * r) * r ^ 2 = a := by
  calc
    r * (a * K ^ 2 * r) * r ^ 2 = a * (K * r ^ 2) ^ 2 := by ring
    _ = a := by rw [hscale]; ring

/-- Exact antipodal cubic inequality in the three-dimensional radial
sparseness argument. Its certificate is
`4(a³+b³)-(a+b)³ = 3(a+b)(a-b)²`. -/
theorem antipodal_cubic_pair
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  have hab : 0 ≤ a + b := add_nonneg ha hb
  have hcert : 0 ≤ 3 * (a + b) * (a - b) ^ 2 := by positivity
  nlinarith

/-- Scalar endgame in the BMO floor for a unit-vector angular profile.
If its second mean deviation is `1-|m|²` and pointwise boundedness gives
`meanSq ≤ 2 meanAbs`, then mean oscillation is at least
`(1-|m|²)/2`. -/
theorem homogeneous_direction_bmo_floor
    {meanAbs meanSq meanNormSq : ℝ}
    (hvariance : meanSq = 1 - meanNormSq)
    (hbounded : meanSq ≤ 2 * meanAbs) :
    (1 - meanNormSq) / 2 ≤ meanAbs := by
  linarith

#print axioms young_three_threeHalves
#print axioms two_half_errors
#print axioms steady_state_bank
#print axioms truncation_chebyshev
#print axioms intermediate_scale_balance
#print axioms critical_damping_exponent_bank
#print axioms local_endpoint_split
#print axioms zero_data_energy_rigidity
#print axioms stationary_energy_rigidity
#print axioms critical_witness_work_lower
#print axioms parabolic_work_normalization
#print axioms antipodal_cubic_pair
#print axioms homogeneous_direction_bmo_floor

end NavierStokesBank
