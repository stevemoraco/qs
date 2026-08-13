import Mathlib

/-!
# Navier--Stokes replicated-amplifier anisotropic energy tax

This file formalizes finite real-amplitude identities only.  It does not define
velocity fields, Fourier packets, the Leray projector, Navier--Stokes
solutions, invariant manifolds, or blow-up.
-/

namespace MillenniumBraid
namespace B2Round41NS

noncomputable def mean (a b : ℝ) : ℝ := (a + b) / 2

def defect (a b : ℝ) : ℝ := a - b

def synchronizedStep (g κ a b : ℝ) : ℝ × ℝ :=
  (g * a - κ * (a - b), g * b + κ * (a - b))

def energy (a b : ℝ) : ℝ := a ^ 2 + b ^ 2

/-- Euclidean energy splits orthogonally into diagonal mean energy and
antisymmetric defect energy. -/
theorem energy_mean_defect (a b : ℝ) :
    energy a b = 2 * (mean a b) ^ 2 + (defect a b) ^ 2 / 2 := by
  unfold energy mean defect
  ring

/-- Exact synchronized-step energy decomposition. -/
theorem synchronized_energy_decomposition (g κ a b : ℝ) :
    energy (synchronizedStep g κ a b).1
        (synchronizedStep g κ a b).2 =
      2 * (g * mean a b) ^ 2 +
        ((g - 2 * κ) * defect a b) ^ 2 / 2 := by
  unfold energy synchronizedStep mean defect
  ring

/-- On the tangent diagonal, synchronization is invisible and the energy
multiplier is exactly `g^2`. -/
theorem diagonal_energy_ratio (g κ a : ℝ) :
    energy (synchronizedStep g κ a a).1
        (synchronizedStep g κ a a).2 =
      g ^ 2 * energy a a := by
  unfold energy synchronizedStep
  ring

/-- Midpoint synchronization kills the transverse defect exactly. -/
theorem midpoint_kills_defect (g a b : ℝ) :
    defect (synchronizedStep g (g / 2) a b).1
        (synchronizedStep g (g / 2) a b).2 = 0 := by
  unfold defect synchronizedStep
  ring

/-- Any strict tangent gain expands nonzero diagonal energy, independently of
the synchronization strength. -/
theorem tangent_gain_forces_total_energy_expansion
    {g a : ℝ} (κ : ℝ) (hg : 1 < g) (ha : a ≠ 0) :
    energy a a <
      energy (synchronizedStep g κ a a).1
        (synchronizedStep g κ a a).2 := by
  rw [diagonal_energy_ratio]
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  have hE : 0 < energy a a := by
    unfold energy
    nlinarith
  have hg2 : 1 < g ^ 2 := by
    nlinarith
  have hprod : 0 < (g ^ 2 - 1) * energy a a :=
    mul_pos (sub_pos.mpr hg2) hE
  nlinarith

/-- Even exact one-step removal of the normal defect does not make the full
map energy-contracting when the tangent gain exceeds one. -/
theorem exact_sync_still_expands_tangent
    {g a : ℝ} (hg : 1 < g) (ha : a ≠ 0) :
    energy a a <
      energy (synchronizedStep g (g / 2) a a).1
        (synchronizedStep g (g / 2) a a).2 := by
  exact tangent_gain_forces_total_energy_expansion (g / 2) hg ha

#print axioms energy_mean_defect
#print axioms synchronized_energy_decomposition
#print axioms diagonal_energy_ratio
#print axioms midpoint_kills_defect
#print axioms tangent_gain_forces_total_energy_expansion
#print axioms exact_sync_still_expands_tangent

end B2Round41NS
end MillenniumBraid
