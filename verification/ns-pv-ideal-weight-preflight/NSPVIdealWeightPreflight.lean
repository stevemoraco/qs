import Mathlib

/-!
Finite real-algebra firewall for the weighted RSS comparison route.

This file proves only that the core/tail comparison factor used by the
weighted-shear transfer is always at least one.  Consequently, if the
ideal flat-weight / zero-tail inequality already fails, no worse positive
condition number can make the comparison strict.

It does not formalize weighted function spaces, adjoint kernels, RSS,
Pineau--Vicol, Navier--Stokes, or any Millennium statement.
-/

namespace NSPVIdealWeightPreflight

/-- The core/tail condition-number factor is at least one. -/
theorem conditionNumberFactor_ge_one
    {M m tau : ℝ}
    (hm : 0 < m)
    (hMm : m ≤ M)
    (htau0 : 0 ≤ tau)
    (htau1 : tau < 1) :
    1 ≤ M / (m * (1 - tau)) := by
  have hden : 0 < m * (1 - tau) :=
    mul_pos hm (sub_pos.mpr htau1)
  have hmtau : m * (1 - tau) ≤ m := by
    nlinarith [mul_nonneg (le_of_lt hm) htau0]
  have hdenM : m * (1 - tau) ≤ M := hmtau.trans hMm
  exact (le_div_iff₀ hden).2 (by simpa using hdenM)

/-- Any strict weighted comparison already implies the ideal comparison. -/
theorem weightedExclusion_requires_idealPreflight
    {M m tau kappa target : ℝ}
    (hm : 0 < m)
    (hMm : m ≤ M)
    (htau0 : 0 ≤ tau)
    (htau1 : tau < 1)
    (htarget : M / (m * (1 - tau)) * kappa ^ 2 < target) :
    kappa ^ 2 < target := by
  have hfactor : 1 ≤ M / (m * (1 - tau)) :=
    conditionNumberFactor_ge_one hm hMm htau0 htau1
  have hk2 : 0 ≤ kappa ^ 2 := sq_nonneg kappa
  have hle : kappa ^ 2 ≤ M / (m * (1 - tau)) * kappa ^ 2 := by
    nlinarith
  exact lt_of_le_of_lt hle htarget

/-- If the ideal inequality fails, no admissible core/tail factor can rescue it. -/
theorem noWeightedRescue_of_idealFailure
    {M m tau kappa target : ℝ}
    (hm : 0 < m)
    (hMm : m ≤ M)
    (htau0 : 0 ≤ tau)
    (htau1 : tau < 1)
    (hideal : target ≤ kappa ^ 2) :
    ¬ (M / (m * (1 - tau)) * kappa ^ 2 < target) := by
  intro hstrict
  have hpre : kappa ^ 2 < target :=
    weightedExclusion_requires_idealPreflight hm hMm htau0 htau1 hstrict
  exact (not_lt_of_ge hideal) hpre

/-- With the RSS resonance target, the square preflight is unavoidable. -/
theorem rssTarget_requires_idealSquareGap
    {M m tau kappa alpha : ℝ}
    (hm : 0 < m)
    (hMm : m ≤ M)
    (htau0 : 0 ≤ tau)
    (htau1 : tau < 1)
    (hstrict :
      M / (m * (1 - tau)) * kappa ^ 2 < 1 / (4 * alpha ^ 2)) :
    kappa ^ 2 < 1 / (4 * alpha ^ 2) := by
  exact weightedExclusion_requires_idealPreflight
    hm hMm htau0 htau1 hstrict

/-- The formal best case `M=m`, `tau=0` has condition-number factor exactly one. -/
theorem flatWeight_zeroTail_factor
    {m : ℝ} (hm : m ≠ 0) :
    m / (m * (1 - 0)) = 1 := by
  simp [hm]

#print axioms conditionNumberFactor_ge_one
#print axioms weightedExclusion_requires_idealPreflight
#print axioms noWeightedRescue_of_idealFailure
#print axioms rssTarget_requires_idealSquareGap
#print axioms flatWeight_zeroTail_factor

end NSPVIdealWeightPreflight
