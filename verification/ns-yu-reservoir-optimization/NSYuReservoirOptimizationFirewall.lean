import Mathlib

noncomputable section

/-!
# Navier--Stokes: optimized Yu-reservoir absorption firewall

Finite algebra extracted from the audit of Runlong Yu,
`arXiv:2606.27560v1` (25 Jun 2026), stacked on
`NSYuReservoirAbsorptionGate.lean`.

If a separate PDE estimate gives `O <= kappa P`, Yu's near-field bound has,
after writing `delta = 1-epsilon`, a coefficient of the schematic form

`delta + A / delta`,

where `A` contains the reservoir coefficient, local energy, filter-ratio loss,
and `kappa`.  Clearing the positive denominator gives

`delta^2 + A < delta`.

The exact scalar feasibility condition is `4 A < 1`.  Thus freedom in the
Young/epsilon parameter does not remove the need for a genuine smallness
margin in the native PDE quantity.

The final two-point identity records the independent coherent-mode obstruction:
difference/diffusion controls only the oscillatory part of a reservoir and
cannot see a nonzero constant mode.

This file proves only finite real algebra.  It does not formalize Yu's PDE
theorem, a Poincare/Korn estimate, Navier--Stokes regularity, or blowup.
-/

namespace NSYuReservoirOptimizationFirewall

/-- Necessity after clearing the Young denominator.  Any strict coefficient
margin `delta^2 + A < delta` forces the discriminant condition `4*A < 1`.
The cleared polynomial implication itself does not need a sign assumption. -/
theorem clearedYoungMargin_forces_quarter
    (A delta : ℝ)
    (hmargin : delta ^ 2 + A < delta) :
    4 * A < 1 := by
  nlinarith [sq_nonneg (2 * delta - 1)]

/-- The discriminant condition is also sufficient: the explicit positive choice
`delta = 1/2` works. -/
theorem quarterMargin_suffices_at_half
    (A : ℝ)
    (hA : 4 * A < 1) :
    ((1 : ℝ) / 2) ^ 2 + A < (1 : ℝ) / 2 := by
  nlinarith

/-- Exact denominator-free feasibility criterion for optimizing the retained
near-field diffusion coefficient against a reciprocal reservoir penalty. -/
theorem existsStrictYoungMargin_iff
    (A : ℝ) :
    (∃ delta : ℝ, 0 < delta ∧ delta ^ 2 + A < delta) ↔ 4 * A < 1 := by
  constructor
  · rintro ⟨delta, _hdelta, hmargin⟩
    exact clearedYoungMargin_forces_quarter A delta hmargin
  · intro hA
    exact ⟨(1 : ℝ) / 2, by norm_num, quarterMargin_suffices_at_half A hA⟩

/-- Exact two-point mean/oscillation decomposition.  This is the finite shadow
of splitting filtered vorticity into a coherent spatial mode plus fluctuation. -/
theorem twoPointReservoir_decomposition (x y : ℝ) :
    x ^ 2 + y ^ 2 = ((x - y) ^ 2 + (x + y) ^ 2) / 2 := by
  ring

/-- A nonzero coherent mode has zero difference cost but positive reservoir.
Hence no finite multiplier on a difference/diffusion term can dominate the
full reservoir before the coherent mode is separately handled. -/
theorem coherentMode_escapes_differenceAbsorption
    (c kappa : ℝ)
    (hc : c ≠ 0) :
    ¬ (c ^ 2 + c ^ 2 ≤ kappa * (c - c) ^ 2) := by
  intro h
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  nlinarith

#print axioms clearedYoungMargin_forces_quarter
#print axioms quarterMargin_suffices_at_half
#print axioms existsStrictYoungMargin_iff
#print axioms twoPointReservoir_decomposition
#print axioms coherentMode_escapes_differenceAbsorption

end NSYuReservoirOptimizationFirewall
