import Mathlib

/-!
# Replicated-amplifier normal-hyperbolicity firewall

This file formalizes only the finite two-replica amplitude algebra behind a
current Navier–Stokes packet-manifold route. It does not define a velocity
field, Fourier packet, Navier–Stokes solution, invariant manifold, or blow-up.
-/

namespace NSReplicatedAmplifierFirewall

/-- Mean amplitude of two replicated catalyst molecules. -/
noncomputable def mean (a b : ℝ) : ℝ := (a + b) / 2

/-- Replica defect transverse to the diagonal one-amplitude line. -/
def defect (a b : ℝ) : ℝ := a - b

/-- Two uncoupled replicas with one common amplification multiplier. -/
def replicatedStep (g a b : ℝ) : ℝ × ℝ := (g * a, g * b)

/-- Two replicas with a sign-definite synchronization coupling. -/
def synchronizedStep (g κ a b : ℝ) : ℝ × ℝ :=
  (g * a - κ * (a - b), g * b + κ * (a - b))

/-- BANKER: the diagonal mean mode is multiplied by the common gain. -/
theorem replicated_mean (g a b : ℝ) :
    mean (replicatedStep g a b).1 (replicatedStep g a b).2 =
      g * mean a b := by
  unfold mean replicatedStep
  ring

/-- BANKER: the transverse replica defect receives exactly the same gain. -/
theorem replicated_defect (g a b : ℝ) :
    defect (replicatedStep g a b).1 (replicatedStep g a b).2 =
      g * defect a b := by
  simp [defect, replicatedStep]
  ring

/-- Exact antisymmetric witness for the replicated normal mode. -/
theorem replicated_antisymmetric_mode_exact (g : ℝ) :
    defect (replicatedStep g 1 (-1)).1
      (replicatedStep g 1 (-1)).2 = 2 * g := by
  simp [defect, replicatedStep]
  ring

/-- CRITIC: with positive common gain and no synchronization, no fixed strict
relative normal-contraction factor `q<1` is possible even on the minimal
antisymmetric mode. -/
theorem zero_sync_cannot_give_strict_relative_contraction
    {g q : ℝ} (hg : 0 < g) (hq : q < 1) :
    ¬ defect (replicatedStep g 1 (-1)).1
        (replicatedStep g 1 (-1)).2 ≤ q * (2 * g) := by
  intro h
  simp [defect, replicatedStep] at h
  nlinarith

/-- CLEANER: synchronization preserves the mean multiplier exactly. -/
theorem synchronized_mean (g κ a b : ℝ) :
    mean (synchronizedStep g κ a b).1
        (synchronizedStep g κ a b).2 = g * mean a b := by
  unfold mean synchronizedStep
  ring

/-- CLEANER: synchronization changes only the replica-defect multiplier, from
`g` to `g-2κ`. -/
theorem synchronized_defect (g κ a b : ℝ) :
    defect (synchronizedStep g κ a b).1
        (synchronizedStep g κ a b).2 =
      (g - 2 * κ) * defect a b := by
  simp [defect, synchronizedStep]
  ring

/-- The exact two-replica synchronization window for relative contraction. -/
theorem synchronization_window_iff (g κ q : ℝ) :
    |g - 2 * κ| ≤ q * g ↔
      ((1 - q) * g) / 2 ≤ κ ∧ κ ≤ ((1 + q) * g) / 2 := by
  constructor
  · intro h
    have hl : -(q * g) ≤ g - 2 * κ := (abs_le.mp h).1
    have hu : g - 2 * κ ≤ q * g := (abs_le.mp h).2
    constructor <;> linarith
  · rintro ⟨hl, hu⟩
    apply abs_le.mpr
    constructor <;> linarith

/-- The exact window is sufficient for relative defect contraction for every
pair of replica amplitudes. -/
theorem synchronized_step_relative_contraction
    {g κ q a b : ℝ}
    (hwindow : |g - 2 * κ| ≤ q * g) :
    |defect (synchronizedStep g κ a b).1
        (synchronizedStep g κ a b).2| ≤
      q * g * |defect a b| := by
  rw [synchronized_defect, abs_mul]
  exact mul_le_mul_of_nonneg_right hwindow (abs_nonneg (defect a b))

/-- For a nonzero replica defect, the synchronization window is also
necessary. -/
theorem nonzero_defect_contraction_forces_window
    {g κ q a b : ℝ}
    (hab : a ≠ b)
    (hcontract :
      |defect (synchronizedStep g κ a b).1
          (synchronizedStep g κ a b).2| ≤
        q * g * |defect a b|) :
    |g - 2 * κ| ≤ q * g := by
  rw [synchronized_defect, abs_mul] at hcontract
  have hd0 : defect a b ≠ 0 := by
    simpa [defect] using sub_ne_zero.mpr hab
  have hd : 0 < |defect a b| := abs_pos.mpr hd0
  by_contra hnot
  have hgt : q * g < |g - 2 * κ| := lt_of_not_ge hnot
  have hmul :
      q * g * |defect a b| < |g - 2 * κ| * |defect a b| :=
    mul_lt_mul_of_pos_right hgt hd
  exact (not_lt_of_ge hcontract) hmul

/-- Midpoint synchronization kills the two-replica defect in one exact step. -/
theorem half_gain_synchronization_kills_defect (g a b : ℝ) :
    defect (synchronizedStep g (g / 2) a b).1
        (synchronizedStep g (g / 2) a b).2 = 0 := by
  rw [synchronized_defect]
  ring

/-- A fixed relative normal gap requires synchronization of a fixed positive
fraction of the common gain; an `o(g)` coupling cannot supply it. -/
theorem fixed_relative_contraction_requires_nonperturbative_sync
    {g κ q : ℝ}
    (hg : 0 < g)
    (hq : q < 1)
    (hcontract : |g - 2 * κ| ≤ q * g) :
    0 < κ ∧ ((1 - q) * g) / 2 ≤ κ := by
  have hw := (synchronization_window_iff g κ q).1 hcontract
  have h1q : 0 < 1 - q := sub_pos.mpr hq
  have hlow : 0 < ((1 - q) * g) / 2 :=
    div_pos (mul_pos h1q hg) (by norm_num)
  exact ⟨lt_of_lt_of_le hlow hw.1, hw.1⟩

/-- CRITIC: any synchronization budget strictly below the sharp lower endpoint
cannot produce the target relative contraction factor. -/
theorem subthreshold_sync_cannot_contract
    {g κ q : ℝ}
    (hsmall : κ < ((1 - q) * g) / 2) :
    ¬ |g - 2 * κ| ≤ q * g := by
  intro h
  exact (not_le_of_gt hsmall) ((synchronization_window_iff g κ q).1 h).1

#print axioms replicated_mean
#print axioms replicated_defect
#print axioms replicated_antisymmetric_mode_exact
#print axioms zero_sync_cannot_give_strict_relative_contraction
#print axioms synchronized_mean
#print axioms synchronized_defect
#print axioms synchronization_window_iff
#print axioms synchronized_step_relative_contraction
#print axioms nonzero_defect_contraction_forces_window
#print axioms half_gain_synchronization_kills_defect
#print axioms fixed_relative_contraction_requires_nonperturbative_sync
#print axioms subthreshold_sync_cannot_contract

end NSReplicatedAmplifierFirewall
