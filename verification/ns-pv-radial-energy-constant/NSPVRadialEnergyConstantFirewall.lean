import Mathlib

/-!
# Navier–Stokes RSS radial-energy integration-constant firewall

Finite scalar algebra only.

The intended PDE interpretation is the normalized radial RSS energy density
`e(R) = R⁻¹ ∫_{B_R} |U|²`.  The human PDE audit derives an ODE whose right-hand
side is integrable at infinity.  These finite theorems record the exact
no-free-lunch point: even geometrically contracting corrections do not select
the asymptotic integration constant, which may remain strictly positive.

This file does not formalize Pineau–Vicol, the RSS equation, radial integration,
Navier–Stokes regularity, blow-up, or any Clay statement.
-/

noncomputable section

namespace NSPVRadialEnergyConstantFirewall

/-- Dyadic shadow of a critical density with an arbitrary integration constant. -/
def density (c : ℝ) (n : ℕ) : ℝ :=
  c + (1 / 2 : ℝ) ^ n

/-- The excess above the integration constant is exactly the dyadic correction. -/
theorem density_excess (c : ℝ) (n : ℕ) :
    density c n - c = (1 / 2 : ℝ) ^ n := by
  simp [density]

/-- The excess contracts by exactly one half at each dyadic step. -/
theorem density_excess_halves (c : ℝ) (n : ℕ) :
    density c (n + 1) - c =
      (1 / 2 : ℝ) * (density c n - c) := by
  rw [density_excess, density_excess]
  rw [pow_succ]
  ring

/-- Every finite dyadic density remains strictly above its integration constant. -/
theorem density_strictly_above_floor (c : ℝ) (n : ℕ) :
    c < density c n := by
  have hpow : 0 < (1 / 2 : ℝ) ^ n := by positivity
  unfold density
  linarith

/-- A positive integration constant therefore gives a positive density at every stage. -/
theorem positive_floor_never_disappears
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    0 < density c n := by
  exact lt_trans hc (density_strictly_above_floor c n)

/-- Geometric contraction of the excess is compatible with a persistent positive floor. -/
theorem contracting_excess_can_keep_positive_floor
    (c : ℝ) (hc : 0 < c) :
    ∃ x : ℕ → ℝ,
      (∀ n : ℕ, x (n + 1) - c = (1 / 2 : ℝ) * (x n - c)) ∧
      (∀ n : ℕ, 0 < x n) := by
  refine ⟨density c, ?_, ?_⟩
  · intro n
    exact density_excess_halves c n
  · intro n
    exact positive_floor_never_disappears hc n

/-- The same contracting excess law is compatible with two distinct positive floors. -/
theorem contracting_excess_does_not_select_the_floor
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hne : c₁ ≠ c₂) :
    (∃ x : ℕ → ℝ,
      (∀ n : ℕ, x (n + 1) - c₁ = (1 / 2 : ℝ) * (x n - c₁)) ∧
      (∀ n : ℕ, 0 < x n)) ∧
    (∃ y : ℕ → ℝ,
      (∀ n : ℕ, y (n + 1) - c₂ = (1 / 2 : ℝ) * (y n - c₂)) ∧
      (∀ n : ℕ, 0 < y n)) ∧
    c₁ ≠ c₂ := by
  exact ⟨contracting_excess_can_keep_positive_floor c₁ hc₁,
    contracting_excess_can_keep_positive_floor c₂ hc₂, hne⟩

#print axioms density_excess
#print axioms density_excess_halves
#print axioms density_strictly_above_floor
#print axioms positive_floor_never_disappears
#print axioms contracting_excess_can_keep_positive_floor
#print axioms contracting_excess_does_not_select_the_floor

end NSPVRadialEnergyConstantFirewall
