import Mathlib

/-!
# Type-I critical energy-density firewall

Finite dyadic arithmetic only. This file formalizes the no-free-lunch model
behind the statement that a scale-critical linear raw energy bound does not force
vanishing normalized shell density or sublogarithmic weighted accumulation.

It does not formalize Type-I Navier--Stokes, Pineau--Vicol RSS profiles,
energy measures, blow-downs, or any Millennium statement.
-/

namespace NSPVTypeICriticalDensityFirewall

/-- Dyadic physical radius. -/
def radius (j : ℕ) : ℕ := 2 ^ j

/-- Critical raw shell mass: one radius unit per shell. -/
def rawShellMass (j : ℕ) : ℕ := 2 ^ j

/-- Finite shadow of raw-mass/radius = 1. -/
def normalizedShellCharge (_j : ℕ) : ℕ := 1

@[simp] theorem shell_mass_eq_radius (j : ℕ) :
    rawShellMass j = radius j := by
  rfl

@[simp] theorem normalized_shell_charge_eq_one (j : ℕ) :
    normalizedShellCharge j = 1 := by
  rfl

/-- Exact finite geometric identity: the first N critical shell masses plus one
are the next dyadic radius. -/
theorem raw_prefix_plus_one (N : ℕ) :
    (∑ j in Finset.range N, rawShellMass j) + 1 = radius N := by
  induction N with
  | zero => norm_num [rawShellMass, radius]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      simp only [rawShellMass, radius] at ih ⊢
      rw [pow_succ]
      omega

/-- Thus every finite raw prefix stays below the critical linear radius budget. -/
theorem raw_prefix_le_radius (N : ℕ) :
    (∑ j in Finset.range N, rawShellMass j) ≤ radius N := by
  have h := raw_prefix_plus_one N
  omega

/-- The normalized/logarithmic charge instead grows exactly by one per shell. -/
theorem normalized_prefix_eq_nat (N : ℕ) :
    (∑ j in Finset.range N, normalizedShellCharge j) = N := by
  simp [normalizedShellCharge]

/-- A uniformly critical raw prefix and arbitrarily long normalized plateau
coexist in the same finite model. -/
theorem critical_linear_budget_allows_normalized_plateau (N : ℕ) :
    (∑ j in Finset.range N, rawShellMass j) ≤ radius N ∧
      (∑ j in Finset.range N, normalizedShellCharge j) = N := by
  exact ⟨raw_prefix_le_radius N, normalized_prefix_eq_nat N⟩

#print axioms shell_mass_eq_radius
#print axioms normalized_shell_charge_eq_one
#print axioms raw_prefix_plus_one
#print axioms raw_prefix_le_radius
#print axioms normalized_prefix_eq_nat
#print axioms critical_linear_budget_allows_normalized_plateau

end NSPVTypeICriticalDensityFirewall
