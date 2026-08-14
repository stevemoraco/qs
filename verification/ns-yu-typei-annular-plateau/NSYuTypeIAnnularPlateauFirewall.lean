import Mathlib

noncomputable section

/-!
# Navier--Stokes: Yu Type-I annular plateau firewall

Finite scale arithmetic extracted from Runlong Yu, arXiv:2606.27560v1
(25 Jun 2026), Section 8.  Yu's reassigned far-field estimate contains the
scale-invariant factors `A_j` and `Q_k`; bounded plateaux in both are explicitly
compatible with linear growth of the unweighted Carleson sum.

This file adds one hostile scaling check: the plateau `A_j = Q_j = 1` is also
compatible, at the level of Type-I dimensional bookkeeping, with a summable raw
Leray--Hopf energy/dissipation cost `r_j = 2^{-j}`.  Therefore finite raw energy,
finite raw dissipation, and Type-I scaling alone cannot provide the missing
annular self-improvement.

No field realizing this scalar model is asserted.  No PDE theorem, regularity
criterion, or Navier--Stokes conclusion is formalized here.
-/

namespace NSYuTypeIAnnularPlateauFirewall

def radius (j : ℕ) : ℝ := ((1 : ℝ) / 2) ^ j

def rawShellCost (j : ℕ) : ℝ := radius j

def annularSquareReservoir (j : ℕ) : ℝ := rawShellCost j / radius j

def localEnstrophyAmplitude (j : ℕ) : ℝ := 1 / radius j

def timeLength (j : ℕ) : ℝ := radius j ^ 2

def qSquare (j : ℕ) : ℝ :=
  timeLength j * localEnstrophyAmplitude j ^ 2

def farFieldPlateau : ℕ → ℝ
  | 0 => 1
  | k + 1 => 1 + farFieldPlateau k / 2

def cumulativeFarField : ℕ → ℝ
  | 0 => 0
  | k + 1 => cumulativeFarField k + farFieldPlateau k

@[simp] theorem radius_pos (j : ℕ) : 0 < radius j := by
  unfold radius
  exact pow_pos (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) j

@[simp] theorem radius_ne_zero (j : ℕ) : radius j ≠ 0 :=
  ne_of_gt (radius_pos j)

theorem rawShellCost_sum (N : ℕ) :
    Finset.sum (Finset.range N) rawShellCost =
      2 * (1 - radius N) := by
  induction N with
  | zero => norm_num [rawShellCost, radius]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [rawShellCost, radius, pow_succ]
      ring

theorem rawShellCost_uniform_budget (N : ℕ) :
    Finset.sum (Finset.range N) rawShellCost ≤ 2 := by
  rw [rawShellCost_sum]
  have h : 0 ≤ radius N := le_of_lt (radius_pos N)
  linarith

theorem annularSquareReservoir_plateau (j : ℕ) :
    annularSquareReservoir j = 1 := by
  simp [annularSquareReservoir, rawShellCost, radius_ne_zero]

theorem qSquare_plateau (j : ℕ) : qSquare j = 1 := by
  have hr : radius j ≠ 0 := radius_ne_zero j
  unfold qSquare timeLength localEnstrophyAmplitude
  field_simp [hr]

theorem farFieldPlateau_ge_one (k : ℕ) : 1 ≤ farFieldPlateau k := by
  induction k with
  | zero => simp [farFieldPlateau]
  | succ k ih =>
      simp only [farFieldPlateau]
      nlinarith

theorem cumulativeFarField_linear_lower (N : ℕ) :
    (N : ℝ) ≤ cumulativeFarField N := by
  induction N with
  | zero => simp [cumulativeFarField]
  | succ N ih =>
      simp only [cumulativeFarField]
      have hmu := farFieldPlateau_ge_one N
      norm_num [Nat.cast_succ]
      linarith

theorem typeI_raw_budget_does_not_force_annular_carleson (N j : ℕ) :
    Finset.sum (Finset.range N) rawShellCost ≤ 2 ∧
    annularSquareReservoir j = 1 ∧
    qSquare j = 1 ∧
    (N : ℝ) ≤ cumulativeFarField N := by
  exact ⟨rawShellCost_uniform_budget N,
    annularSquareReservoir_plateau j,
    qSquare_plateau j,
    cumulativeFarField_linear_lower N⟩

#print axioms rawShellCost_sum
#print axioms rawShellCost_uniform_budget
#print axioms annularSquareReservoir_plateau
#print axioms qSquare_plateau
#print axioms farFieldPlateau_ge_one
#print axioms cumulativeFarField_linear_lower
#print axioms typeI_raw_budget_does_not_force_annular_carleson

end NSYuTypeIAnnularPlateauFirewall
