import Mathlib

/-!
# B2 round 63: newest-survivor interface firewalls

Six exact finite/logical checks against the newest surviving research interfaces.
No official Millennium conclusion is asserted.
-/

namespace B2Round63

/-- RH firewall: positive row reserves do not imply positivity of the coupled
quadratic form.  The symmetric matrix [[1,2],[2,1]] has positive row sums but a
negative direction (1,-1). -/
theorem rh_positive_row_reserves_do_not_force_psd :
    (0 : ℝ) < 1 + 2 ∧
    (0 : ℝ) < 2 + 1 ∧
    (1 : ℝ) * 1 ^ 2 + (2 + 2) * 1 * (-1) + 1 * (-1) ^ 2 < 0 := by
  norm_num

/-- A target that is zero on the finite prefix `0,...,N` and becomes nonzero
immediately outside that pool. -/
def pnpFinitePoolTarget (N n : ℕ) : ℕ :=
  if n = N + 1 then 1 else 0

/-- P-vs-NP firewall: exact agreement on an arbitrary finite prefix/pool does
not imply global agreement. -/
theorem pnp_finite_prefix_zero_error_not_global (N : ℕ) :
    (∀ n : ℕ, n ≤ N → pnpFinitePoolTarget N n = 0) ∧
    pnpFinitePoolTarget N (N + 1) = 1 := by
  constructor
  · intro n hn
    have hne : n ≠ N + 1 := by omega
    simp [pnpFinitePoolTarget, hne]
  · simp [pnpFinitePoolTarget]

/-- BSD firewall: any fixed finite congruence precision leaves distinct global
integers.  `1` and `1+M` are congruent modulo positive `M`, but unequal. -/
theorem bsd_finite_congruence_precision_not_exact
    (M : ℕ) (hM : 0 < M) :
    M ∣ ((1 + M) - 1) ∧ 1 + M ≠ 1 := by
  constructor
  · have hdiff : (1 + M) - 1 = M := by omega
    rw [hdiff]
  · omega

/-- Hodge r=3 firewall: the explicit common-root valuation pattern
`(x,y,z)=(2,2,4)` with conductor allocation `k=1` passes all three currently
banked local weight-10/12/14 order inequalities when the external A/B orders
are zero.  Thus those local inequalities alone cannot be a coverage theorem. -/
theorem hodge_224_local_pattern_survives_weight_gates :
    (4 : ℕ) = Nat.min (3 * 2) (2 * 2) ∧
    16 = 3 * 4 + 2 * 2 ∧
    2 = Nat.min (16 - 1) (2 * 1) ∧
    2 ≤ 2 * 4 + 2 * 2 ∧
    2 ≤ 2 * 4 ∧
    2 ≤ 4 + 2 := by
  norm_num

/-- Navier-Stokes/AO firewall: all currently formalized finite Batchelor-center
pitch/admissibility/b-value margins can hold while an independent curvature
slot is zero.  The missing phase-curvature identification therefore cannot be
inferred from those scalar margins alone. -/
theorem ns_finite_anchor_margins_do_not_force_curvature :
    ∃ q beta b curvature : ℝ,
      (3 : ℝ) / 4 < q ∧
      q < 1 ∧
      q / 2 < beta ∧
      beta < 1 / q ∧
      (35 : ℝ) / 243 < b ∧
      curvature = 0 := by
  refine ⟨(4 : ℝ) / 5, (3 : ℝ) / 4, 1, 0, ?_⟩
  norm_num

/-- Quartic perturbation of a scalar weak-coupling recurrence while preserving
all coefficients through cubic order. -/
def quarticRGStep (d u : ℝ) : ℝ :=
  u + u ^ 2 + u ^ 3 + d * u ^ 4

/-- Leading reciprocal-clock progress for the quartic recurrence. -/
noncomputable def quarticReciprocalClockProgress (d u : ℝ) : ℝ :=
  1 / u - 1 / quarticRGStep d u

/-- Yang-Mills normalization firewall: two recurrences agreeing through cubic
order can differ at quartic order. -/
theorem ym_same_cubic_data_quartic_difference (u : ℝ) :
    quarticRGStep 1 u - quarticRGStep 0 u = u ^ 4 := by
  simp [quarticRGStep]

/-- At the concrete weak-coupling test point `u=1/2`, the quartic term changes
the reciprocal-clock progress from 6/7 to 14/15.  Thus even cubic recurrence
data alone do not determine the finite clock normalization. -/
theorem ym_quartic_changes_reciprocal_clock_at_half :
    quarticReciprocalClockProgress 0 ((1 : ℝ) / 2) = (6 : ℝ) / 7 ∧
    quarticReciprocalClockProgress 1 ((1 : ℝ) / 2) = (14 : ℝ) / 15 ∧
    quarticReciprocalClockProgress 0 ((1 : ℝ) / 2) ≠
      quarticReciprocalClockProgress 1 ((1 : ℝ) / 2) := by
  norm_num [quarticReciprocalClockProgress, quarticRGStep]

/-- One kernel-checkable package of all six round-63 interface checks. -/
structure Round63Receipt : Prop where
  rh :
    (0 : ℝ) < 1 + 2 ∧
    (0 : ℝ) < 2 + 1 ∧
    (1 : ℝ) * 1 ^ 2 + (2 + 2) * 1 * (-1) + 1 * (-1) ^ 2 < 0
  pnp : ∀ N : ℕ,
    (∀ n : ℕ, n ≤ N → pnpFinitePoolTarget N n = 0) ∧
    pnpFinitePoolTarget N (N + 1) = 1
  bsd : ∀ M : ℕ, 0 < M → M ∣ ((1 + M) - 1) ∧ 1 + M ≠ 1
  hodge :
    (4 : ℕ) = Nat.min (3 * 2) (2 * 2) ∧
    16 = 3 * 4 + 2 * 2 ∧
    2 = Nat.min (16 - 1) (2 * 1) ∧
    2 ≤ 2 * 4 + 2 * 2 ∧
    2 ≤ 2 * 4 ∧
    2 ≤ 4 + 2
  ns :
    ∃ q beta b curvature : ℝ,
      (3 : ℝ) / 4 < q ∧ q < 1 ∧ q / 2 < beta ∧ beta < 1 / q ∧
      (35 : ℝ) / 243 < b ∧ curvature = 0
  ymDifference : ∀ u : ℝ,
    quarticRGStep 1 u - quarticRGStep 0 u = u ^ 4
  ymClock :
    quarticReciprocalClockProgress 0 ((1 : ℝ) / 2) = (6 : ℝ) / 7 ∧
    quarticReciprocalClockProgress 1 ((1 : ℝ) / 2) = (14 : ℝ) / 15 ∧
    quarticReciprocalClockProgress 0 ((1 : ℝ) / 2) ≠
      quarticReciprocalClockProgress 1 ((1 : ℝ) / 2)

theorem round63_receipt : Round63Receipt where
  rh := rh_positive_row_reserves_do_not_force_psd
  pnp := pnp_finite_prefix_zero_error_not_global
  bsd := bsd_finite_congruence_precision_not_exact
  hodge := hodge_224_local_pattern_survives_weight_gates
  ns := ns_finite_anchor_margins_do_not_force_curvature
  ymDifference := ym_same_cubic_data_quartic_difference
  ymClock := ym_quartic_changes_reciprocal_clock_at_half

#print axioms rh_positive_row_reserves_do_not_force_psd
#print axioms pnp_finite_prefix_zero_error_not_global
#print axioms bsd_finite_congruence_precision_not_exact
#print axioms hodge_224_local_pattern_survives_weight_gates
#print axioms ns_finite_anchor_margins_do_not_force_curvature
#print axioms ym_same_cubic_data_quartic_difference
#print axioms ym_quartic_changes_reciprocal_clock_at_half
#print axioms round63_receipt

end B2Round63
