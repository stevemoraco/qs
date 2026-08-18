import Mathlib

/-!
# Engineering degree is not Wiener-chaos degree

Finite two-channel shadow of the Faizal--Shabir weak-coupling localization
problem.

At the Gaussian linearization, a marginal quadratic gauge invariant and a
strictly irrelevant derivative-quadratic gauge invariant can both lie in the
second Wiener chaos.  A projection that removes only the marginal coordinate
is an orthogonal idempotent, but its complement still contains a second-chaos
mode.  Consequently a second-quantized Gaussian step contracts that surviving
mode by `rho^2`, not by the `rho^3` bound available on the full chaos-order
`> 2` complement.

The correct repair needs a joint engineering/chaos grading (or another native
scale factor), not a raw polynomial-degree cutoff alone.

This file is finite real algebra.  It does not formalize gauge fields, Wiener
chaos, polymer norms, renormalization, Yang--Mills, a mass gap, or a Clay
theorem.
-/

namespace Millennium.YangMills.EngineeringChaosMismatchFirewall

/-- Euclidean pairing on a two-dimensional shadow with one marginal and one
engineering-irrelevant coordinate. -/
def pairInner (u v : ℝ × ℝ) : ℝ :=
  u.1 * v.1 + u.2 * v.2

/-- Projection onto the marginal coordinate. -/
def marginalProjection (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.1, 0)

/-- A Gaussian noise step acting with the same second-chaos multiplier on both
quadratic channels. -/
def secondChaosStep (rho : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (rho ^ 2 * v.1, rho ^ 2 * v.2)

/-- The marginal quadratic mode. -/
def marginalMode : ℝ × ℝ := (1, 0)

/-- A derivative-quadratic mode: engineering-irrelevant but still quadratic in
the Gaussian field. -/
def engineeringIrrelevantMode : ℝ × ℝ := (0, 1)

/-- The marginal projection is idempotent. -/
theorem marginalProjection_idempotent (v : ℝ × ℝ) :
    marginalProjection (marginalProjection v) = marginalProjection v := by
  rcases v with ⟨x, y⟩
  rfl

/-- The marginal projection is self-adjoint for the Euclidean pairing. -/
theorem marginalProjection_selfAdjoint (u v : ℝ × ℝ) :
    pairInner (marginalProjection u) v =
      pairInner u (marginalProjection v) := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  simp [pairInner, marginalProjection]

/-- The source-style engineering split removes the marginal mode. -/
theorem marginalProjection_fixes_marginal :
    marginalProjection marginalMode = marginalMode := by
  rfl

/-- The source-style engineering split retains the derivative-quadratic mode in
its complement. -/
theorem marginalProjection_kills_engineeringIrrelevant :
    marginalProjection engineeringIrrelevantMode = (0, 0) := by
  rfl

/-- Pure chaos order is blind to the engineering distinction: both channels
receive exactly the same multiplier `rho^2`. -/
theorem secondChaosStep_blind_to_engineering_degree (rho : ℝ) :
    secondChaosStep rho marginalMode = (rho ^ 2, 0) ∧
      secondChaosStep rho engineeringIrrelevantMode = (0, rho ^ 2) := by
  constructor <;>
    simp [secondChaosStep, marginalMode, engineeringIrrelevantMode]

/-- On the open unit interval, the second-chaos multiplier is strictly larger
than the third-chaos multiplier. -/
theorem second_power_strictly_exceeds_third
    (rho : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    rho ^ 3 < rho ^ 2 := by
  have hsq : 0 < rho ^ 2 := pow_pos hrho0 2
  have hone : 0 < 1 - rho := sub_pos.mpr hrho1
  have hprod : 0 < rho ^ 2 * (1 - rho) := mul_pos hsq hone
  nlinarith

/-- Therefore projecting out only the marginal coordinate does not upgrade the
surviving engineering-irrelevant quadratic mode to a third-chaos contraction. -/
theorem engineering_irrelevant_mode_not_high_chaos_contracted
    (rho : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    rho ^ 3 * engineeringIrrelevantMode.2 <
      (secondChaosStep rho engineeringIrrelevantMode).2 := by
  simpa [engineeringIrrelevantMode, secondChaosStep] using
    second_power_strictly_exceeds_third rho hrho0 hrho1

/-- No projection can simultaneously be the identity on the entire quadratic
chaos and remove only the engineering-irrelevant quadratic coordinate.  This
is the finite range mismatch between a full low-polynomial projection and the
source's selective engineering projection. -/
theorem no_full_second_chaos_projection_realizes_engineering_split :
    ¬ ∃ P : (ℝ × ℝ) → (ℝ × ℝ),
        (∀ v, P v = v) ∧
        P marginalMode = marginalMode ∧
        P engineeringIrrelevantMode = (0, 0) := by
  rintro ⟨P, hfull, hmarginal, hirrelevant⟩
  have h := hfull engineeringIrrelevantMode
  rw [hirrelevant] at h
  have hsnd := congrArg Prod.snd h
  norm_num [engineeringIrrelevantMode] at hsnd

/-- A joint engineering factor can repair the missing exponent. -/
def jointEngineeringStep (rho eta : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (rho ^ 2 * v.1, rho ^ 2 * eta * v.2)

/-- If the extra engineering-scale factor is at most `rho`, then the surviving
quadratic irrelevant mode does obey the third-power bound. -/
theorem engineering_factor_recovers_third_power
    (rho eta : ℝ) (heta : eta ≤ rho) :
    (jointEngineeringStep rho eta engineeringIrrelevantMode).2 ≤ rho ^ 3 := by
  change rho ^ 2 * eta ≤ rho ^ 3
  calc
    rho ^ 2 * eta ≤ rho ^ 2 * rho :=
      mul_le_mul_of_nonneg_left heta (sq_nonneg rho)
    _ = rho ^ 3 := by ring

#print axioms marginalProjection_idempotent
#print axioms marginalProjection_selfAdjoint
#print axioms marginalProjection_fixes_marginal
#print axioms marginalProjection_kills_engineeringIrrelevant
#print axioms secondChaosStep_blind_to_engineering_degree
#print axioms second_power_strictly_exceeds_third
#print axioms engineering_irrelevant_mode_not_high_chaos_contracted
#print axioms no_full_second_chaos_projection_realizes_engineering_split
#print axioms engineering_factor_recovers_third_power

end Millennium.YangMills.EngineeringChaosMismatchFirewall
