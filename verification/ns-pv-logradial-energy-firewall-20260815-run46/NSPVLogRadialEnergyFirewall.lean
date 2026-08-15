import Mathlib

/-!
# Pineau--Vicol log-radius action versus raw energy: finite firewall

Finite dyadic algebra only.  This file formalizes the source-shaped fact that a
geometrically summable raw shell budget can coexist with order-one normalized
log-radius action on every shell.

It does NOT formalize logarithmic coordinates, angular Fourier modes,
Pineau--Vicol, rotated self-similar profiles, Navier--Stokes, or a Clay theorem.
-/

namespace NSPVLogRadialEnergyFirewall

/-- Source-shaped raw shell budget: the physical Dirichlet contribution gains
one dyadic factor. -/
def rawShell (j : ℕ) : ℚ := (1 / 2 : ℚ) ^ (j + 1)

/-- Source-shaped normalized log-radius action: the resonant phase carries
order-one action on each logarithmic shell. -/
def normalizedAction (_j : ℕ) : ℚ := 1

/-- Exact geometric prefix identity. -/
theorem rawPrefix_exact (N : ℕ) :
    (Finset.range N).sum rawShell = 1 - (1 / 2 : ℚ) ^ N := by
  induction N with
  | zero =>
      simp [rawShell]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [rawShell]
      rw [pow_succ]
      ring

/-- Every finite raw-energy prefix is uniformly bounded by one. -/
theorem rawPrefix_le_one (N : ℕ) :
    (Finset.range N).sum rawShell ≤ 1 := by
  rw [rawPrefix_exact]
  have hpow : 0 ≤ (1 / 2 : ℚ) ^ N := by positivity
  linarith

/-- The corresponding normalized action prefix grows exactly linearly. -/
theorem normalizedActionPrefix_exact (N : ℕ) :
    (Finset.range N).sum normalizedAction = (N : ℚ) := by
  simp [normalizedAction]

/-- Finite no-free-lunch package: an arbitrarily long prefix can have uniformly
bounded raw energy while retaining one full unit of normalized action per shell. -/
theorem boundedRawBudget_with_linearNormalizedAction (N : ℕ) :
    (Finset.range N).sum rawShell ≤ 1 ∧
      (Finset.range N).sum normalizedAction = (N : ℚ) := by
  exact ⟨rawPrefix_le_one N, normalizedActionPrefix_exact N⟩

#print axioms rawPrefix_exact
#print axioms rawPrefix_le_one
#print axioms normalizedActionPrefix_exact
#print axioms boundedRawBudget_with_linearNormalizedAction

end NSPVLogRadialEnergyFirewall
