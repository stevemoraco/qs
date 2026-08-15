import Mathlib

/-!
# Pineau--Vicol one-slice regularity: finite drift-action firewall

Finite order/sum algebra only.

Pineau--Vicol arXiv:2607.09619v2 proves a local Type-I regularity criterion:
under their PDE hypotheses, one sufficiently late self-similar time slice with
small self-similar time derivative forces regularity.  The first theorem below
formalizes only the logical contrapositive of an abstract one-slice trigger.
The remaining theorems record the finite action consequence, the exact residual
budget that would make such a drift floor useful in a Yu-style recurrence, and
a bounded oscillatory countermodel showing that a uniform motion floor alone
does not force escape or non-precompactness.

No theorem below formalizes Pineau--Vicol's PDE hypotheses, self-similar
coordinates, Yu's filtered estimates, Navier--Stokes, or any Millennium Prize
statement.
-/

namespace NSPVDriftActionFloor

/-- If any late slice with `speed ≤ δ` would imply regularity, then failure of
regularity forces a strict speed floor on every late slice. -/
theorem no_small_late_slice_of_one_slice_regularizer
    {ι : Type*} [Preorder ι]
    {s0 : ι} {δ : ℝ} {speed : ι → ℝ} {Regular : Prop}
    (trigger : ∀ s, s0 ≤ s → speed s ≤ δ → Regular)
    (hbad : ¬ Regular) :
    ∀ s, s0 ≤ s → δ < speed s := by
  intro s hs
  by_contra hnot
  have hle : speed s ≤ δ := le_of_not_gt hnot
  exact hbad (trigger s hs hle)

theorem finite_action_has_linear_floor
    {N : ℕ} {δ : ℝ} {speed : Fin N → ℝ}
    (hfloor : ∀ k, δ ≤ speed k) :
    (N : ℝ) * δ ≤ ∑ k, speed k := by
  calc
    (N : ℝ) * δ = ∑ _k : Fin N, δ := by simp
    _ ≤ ∑ k, speed k := by
      exact Finset.sum_le_sum fun k _hk => hfloor k

theorem action_below_linear_floor_forces_small_slice
    {N : ℕ} {δ : ℝ} {speed : Fin N → ℝ}
    (hbudget : ∑ k, speed k < (N : ℝ) * δ) :
    ∃ k, speed k < δ := by
  by_contra hno
  have hpoint : ∀ k, δ ≤ speed k := by
    intro k
    exact le_of_not_gt fun hk => hno ⟨k, hk⟩
  have hfloor := finite_action_has_linear_floor
    (N := N) (δ := δ) (speed := speed) hpoint
  linarith

theorem finite_action_budget_forces_regular_slice
    {N : ℕ} {δ : ℝ} {speed : Fin N → ℝ} {Regular : Prop}
    (trigger : ∀ k, speed k ≤ δ → Regular)
    (hbudget : ∑ k, speed k < (N : ℝ) * δ) :
    Regular := by
  rcases action_below_linear_floor_forces_small_slice
      (N := N) (δ := δ) (speed := speed) hbudget with ⟨k, hk⟩
  exact trigger k (le_of_lt hk)

theorem residual_charge_has_linear_floor
    {N : ℕ} {δ c : ℝ} {speed residual : Fin N → ℝ}
    (hc : 0 ≤ c)
    (hspeed : ∀ k, δ ≤ speed k)
    (hcharge : ∀ k, c * speed k ≤ residual k) :
    (N : ℝ) * (c * δ) ≤ ∑ k, residual k := by
  calc
    (N : ℝ) * (c * δ) = ∑ _k : Fin N, c * δ := by simp
    _ ≤ ∑ k, residual k := by
      exact Finset.sum_le_sum fun k _hk =>
        le_trans (mul_le_mul_of_nonneg_left (hspeed k) hc) (hcharge k)

theorem residual_budget_below_drift_floor_forces_regularity
    {N : ℕ} {δ c : ℝ} {speed residual : Fin N → ℝ} {Regular : Prop}
    (hc : 0 ≤ c)
    (trigger : ∀ k, speed k ≤ δ → Regular)
    (hcharge : ∀ k, c * speed k ≤ residual k)
    (hbudget : ∑ k, residual k < (N : ℝ) * (c * δ)) :
    Regular := by
  by_contra hbad
  have hspeed : ∀ k, δ ≤ speed k := by
    intro k
    by_contra hnot
    have hlt : speed k < δ := lt_of_not_ge hnot
    exact hbad (trigger k (le_of_lt hlt))
  have hfloor := residual_charge_has_linear_floor
    (N := N) (δ := δ) (c := c) (speed := speed) (residual := residual)
    hc hspeed hcharge
  linarith

theorem bounded_two_cycle (n : ℕ) :
    |((-1 : ℝ) ^ n)| = 1 := by
  simp

theorem bounded_two_cycle_has_persistent_motion (n : ℕ) :
    |((-1 : ℝ) ^ (n + 1)) - ((-1 : ℝ) ^ n)| = 2 := by
  rw [pow_succ]
  calc
    |(-1 : ℝ) ^ n * (-1) - (-1 : ℝ) ^ n| =
        |(-2 : ℝ) * (-1 : ℝ) ^ n| := by
          congr 1
          ring
    _ = 2 := by simp [abs_mul]

theorem persistent_motion_does_not_force_escape :
    ∀ n : ℕ,
      |((-1 : ℝ) ^ n)| = 1 ∧
      |((-1 : ℝ) ^ (n + 1)) - ((-1 : ℝ) ^ n)| = 2 := by
  intro n
  exact ⟨bounded_two_cycle n, bounded_two_cycle_has_persistent_motion n⟩

#print axioms no_small_late_slice_of_one_slice_regularizer
#print axioms finite_action_has_linear_floor
#print axioms action_below_linear_floor_forces_small_slice
#print axioms finite_action_budget_forces_regular_slice
#print axioms residual_charge_has_linear_floor
#print axioms residual_budget_below_drift_floor_forces_regularity
#print axioms bounded_two_cycle
#print axioms bounded_two_cycle_has_persistent_motion
#print axioms persistent_motion_does_not_force_escape

end NSPVDriftActionFloor
