import Mathlib

/-!
# Navier--Stokes audit: fixed positive ledger thresholds do not close decay

Honesty status: finite scalar recurrence only. This file does not formalize the
Navier--Stokes equations, axisymmetric flow, a Caccioppoli inequality, packet
selection, or any official Millennium statement.

The protected obstruction is exact: a positive additive ledger term can remain
strictly below a fixed positive activity threshold while supporting a positive
fixed point of an otherwise contractive recurrence. Therefore absence of an
above-threshold ledger event cannot by itself justify deleting the additive term
or replacing it by a superlinear remainder along an iteration whose score tends
to zero.
-/

namespace MillenniumBraid
namespace NSFixedThresholdIteration

/-- The equilibrium of `q_next = theta * q + ledger`. -/
def equilibrium (theta ledger : ℝ) : ℝ :=
  ledger / (1 - theta)

/-- A positive ledger and a contraction factor below one give a positive equilibrium. -/
theorem equilibrium_pos
    (theta ledger : ℝ)
    (htheta : theta < 1)
    (hledger : 0 < ledger) :
    0 < equilibrium theta ledger := by
  simpa [equilibrium] using div_pos hledger (sub_pos.mpr htheta)

/-- The displayed equilibrium is an exact fixed point of the affine recurrence. -/
theorem equilibrium_step
    (theta ledger : ℝ)
    (htheta : theta < 1) :
    theta * equilibrium theta ledger + ledger = equilibrium theta ledger := by
  have hne : 1 - theta ≠ 0 := ne_of_gt (sub_pos.mpr htheta)
  unfold equilibrium
  field_simp [hne]
  ring

/-- A constant sequence at the positive affine equilibrium. -/
def floorSequence (theta threshold : ℝ) : ℕ → ℝ :=
  fun _ => equilibrium theta (threshold / 2)

/--
A positive ledger can be strictly below the fixed activity threshold and still
prevent any decay to zero.  The constant sequence satisfies the recurrence with
equality at every step.
-/
theorem positive_subthreshold_ledger_supports_nondecreasing_floor
    (theta threshold : ℝ)
    (htheta_nonneg : 0 ≤ theta)
    (htheta_lt_one : theta < 1)
    (hthreshold : 0 < threshold) :
    let ledger := threshold / 2
    (0 < ledger) ∧
    (ledger < threshold) ∧
    (∀ n, 0 < floorSequence theta threshold n) ∧
    (∀ n,
      floorSequence theta threshold (n + 1) =
        theta * floorSequence theta threshold n + ledger) := by
  dsimp
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · intro n
    exact equilibrium_pos theta (threshold / 2) htheta_lt_one (by linarith)
  · intro n
    dsimp [floorSequence]
    exact (equilibrium_step theta (threshold / 2) htheta_lt_one).symm

/--
Consequently, the affine upper recurrence together with a fixed positive
subthreshold ledger bound does not force convergence to zero.
-/
theorem affine_decay_claim_has_positive_countermodel
    (theta threshold : ℝ)
    (htheta_nonneg : 0 ≤ theta)
    (htheta_lt_one : theta < 1)
    (hthreshold : 0 < threshold) :
    ∃ q : ℕ → ℝ, ∃ ledger : ℝ,
      0 < ledger ∧ ledger < threshold ∧
      (∀ n, q (n + 1) ≤ theta * q n + ledger) ∧
      (∀ n, 0 < q n) := by
  refine ⟨floorSequence theta threshold, threshold / 2, ?_⟩
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · intro n
    rw [positive_subthreshold_ledger_supports_nondecreasing_floor
      theta threshold htheta_nonneg htheta_lt_one hthreshold |>.2.2.2 n]
  · exact positive_subthreshold_ledger_supports_nondecreasing_floor
      theta threshold htheta_nonneg htheta_lt_one hthreshold |>.2.2.1

#print axioms equilibrium_pos
#print axioms equilibrium_step
#print axioms positive_subthreshold_ledger_supports_nondecreasing_floor
#print axioms affine_decay_claim_has_positive_countermodel

end NSFixedThresholdIteration
end MillenniumBraid
