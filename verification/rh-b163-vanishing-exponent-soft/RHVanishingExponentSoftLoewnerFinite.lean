import Mathlib

/-!
# RH B163 vanishing-exponent soft-Loewner finite core

Finite real-algebra consumers only.

The human B163 reduction weakens B162's fixed soft depth exponent by allowing

  theta_N -> 0,

while lowering the spectral floor to

  tau_N = exp(-b_N),

provided the dimensionless separation ratio

  theta_N * log N / b_N

diverges.  The declarations below formalize only the load-bearing finite
exponent and Rayleigh bookkeeping.  They do not formalize real-power monotonicity,
path Laplacians, matrix spectral theory, Bhattacharya--Martin--Simpson, Landau,
primes, zeta zeros, BGST, B46, or RH.
-/

namespace RHVanishingExponentSoftLoewnerFinite

/-- Exact schedule identity behind the parametrization
`b = logN/L`, `theta = omega/L`.

The division-free form is deliberately used so this theorem is pure field
algebra and does not hide an asymptotic statement. -/
theorem schedule_ratio_identity
    {logN L omega b theta : ℝ}
    (hL : L ≠ 0)
    (hb : b = logN / L)
    (htheta : theta = omega / L) :
    theta * logN = omega * b := by
  rw [hb, htheta]
  field_simp [hL]
  ring

/-- At the finite-ratio strip boundary `Delta = 1/(2*C)`, the depth-to-floor
exponent is exactly one. -/
theorem finite_ratio_strip_boundary
    {C : ℝ} (hC : C ≠ 0) :
    2 * (1 / (2 * C)) * C = 1 := by
  field_simp [hC]

/-- A displacement strictly beyond the finite-ratio strip gives strict exponent
room: `2*Delta*C > 1`. -/
theorem finite_ratio_offstrip_margin
    {Delta C : ℝ}
    (hC : 0 < C)
    (hDelta : 1 / (2 * C) < Delta) :
    1 < 2 * Delta * C := by
  have h2C : 0 < 2 * C := by positivity
  have hmul := mul_lt_mul_of_pos_right hDelta h2C
  field_simp [ne_of_gt hC] at hmul
  nlinarith

/-- The hostile complementary regime: if `2*Delta*C < 1`, multiplying by a
positive floor exponent `b` preserves the strict inequality.  This is the exact
finite arithmetic behind the statement that a finite separation ratio can miss
small off-critical displacement. -/
theorem finite_ratio_blindspot
    {Delta C b : ℝ}
    (hb : 0 < b)
    (hblind : 2 * Delta * C < 1) :
    2 * Delta * C * b < b := by
  nlinarith

/-- If the dimensionless separation factor `C` beats `1/(2 Delta)`, then the
soft-potential exponent `2 Delta C b` beats the floor exponent `b`. -/
theorem depth_exponent_beats_floor
    {Delta C b : ℝ}
    (hb : 0 < b)
    (hmargin : 1 < 2 * Delta * C) :
    b < 2 * Delta * C * b := by
  nlinarith

/-- Compose a kinetic half-budget and a potential half-budget into one spectral
floor budget.  This is the finite scalar endpoint used after the B160A localized
witness is inserted. -/
theorem rayleigh_below_floor_of_half_budgets
    {R floor normSq kinetic potential total : ℝ}
    (hR : 0 < R)
    (hNorm : 0 ≤ normSq)
    (hFloor : 0 ≤ floor)
    (hKinetic : kinetic * R ^ 2 ≤ 128 * normSq)
    (hKineticFloor : 128 / R ^ 2 ≤ floor / 2)
    (hPotential : potential ≤ (floor / 2) * normSq)
    (hTotal : total = kinetic + potential) :
    total ≤ floor * normSq := by
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hK : kinetic ≤ (128 / R ^ 2) * normSq := by
    have hk0 : kinetic ≤ (128 * normSq) / R ^ 2 :=
      (le_div_iff₀ hR2).2 hKinetic
    calc
      kinetic ≤ (128 * normSq) / R ^ 2 := hk0
      _ = (128 / R ^ 2) * normSq := by ring
  have hKF : kinetic ≤ (floor / 2) * normSq := by
    exact hK.trans (mul_le_mul_of_nonneg_right hKineticFloor hNorm)
  calc
    total = kinetic + potential := hTotal
    _ ≤ (floor / 2) * normSq + (floor / 2) * normSq := add_le_add hKF hPotential
    _ = floor * normSq := by ring

/-- If each of two nonnegative localized costs is at most half the target floor,
then their sum is below the floor.  This tiny theorem is used by external
verifiers that already normalized by the witness norm. -/
theorem two_half_costs_below_floor
    {kinetic potential floor : ℝ}
    (hk : kinetic ≤ floor / 2)
    (hp : potential ≤ floor / 2) :
    kinetic + potential ≤ floor := by
  linarith

#print axioms schedule_ratio_identity
#print axioms finite_ratio_strip_boundary
#print axioms finite_ratio_offstrip_margin
#print axioms finite_ratio_blindspot
#print axioms depth_exponent_beats_floor
#print axioms rayleigh_below_floor_of_half_budgets
#print axioms two_half_costs_below_floor

end RHVanishingExponentSoftLoewnerFinite
