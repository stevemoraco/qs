import Mathlib

/-!
# Prime-energy finite core

Finite algebra/order core for the RH prime-energy abscissa lane.

The analytic theorem lives in
`PRIME_ENERGY_ABSCISSA_DEPTH_INVARIANT_2026-08-11.md`.
This file does **not** prove RH.  It records the finite positivity fact used after
lifting a signed prime-window statistic to a quadratic energy: every sampled
energy is a sum of squares, hence nonnegative.
-/

namespace RHProof
namespace PrimeEnergy

open scoped BigOperators

/-- A finite sampled quadratic energy is nonnegative.  This is the algebraic
core behind the PSD Gram lift of the sign-changing prime-window observable. -/
theorem sampled_energy_nonneg
    {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (a : ι → ℝ)
    (v : ι → κ → ℝ) :
    0 ≤ ∑ j : κ, (∑ i : ι, a i * v i j) ^ 2 := by
  positivity

/-- Adding one more nonnegative energy block can only increase accumulated
energy.  Continuous cutoff monotonicity is the integral analogue. -/
theorem energy_accumulation_mono
    (E block : ℝ)
    (hblock : 0 ≤ block) :
    E ≤ E + block := by
  linarith

/-- If all positive damping exponents have finite energy, then any abstract
nonnegative depth bounded above by every positive epsilon must vanish.  This is
the final order-theoretic step after the analytic abscissa theorem. -/
theorem depth_eq_zero_of_le_every_pos
    (depth : ℝ)
    (hdepth : 0 ≤ depth)
    (h : ∀ ε : ℝ, 0 < ε → depth ≤ ε) :
    depth = 0 := by
  apply le_antisymm
  · by_contra hne
    have hpos : 0 < depth := lt_of_le_of_ne hdepth (Ne.symm hne)
    have hhalf := h (depth / 2) (by linarith)
    linarith
  · exact hdepth

end PrimeEnergy
end RHProof
