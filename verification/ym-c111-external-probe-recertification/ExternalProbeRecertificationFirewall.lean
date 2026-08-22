import Mathlib

namespace Millennium.YangMills

open scoped BigOperators

/-!
# External-probe and recertification firewalls

Finite consequences used to audit the complex cluster-expansion repair.

A zero activity annihilates an ordinarily pinned cluster weight.  An external
probe instead supplies a multiplicity-weighted touching-cluster row, from
which the unweighted touching row follows for nonnegative weights.

A fixed inner-tube distance converts first and second Cauchy rows into one
fixed recertification multiplier.  Merely knowing that the compact row tends
to zero is insufficient when the multiplier varies with the same regulator.

This file proves finite real algebra only.  It does not formalize the source
field theory, continuum reconstruction, a mass gap, or a prize theorem.
-/

theorem zero_activity_pinned_cluster_vanishes (clusterWeight : ℝ) :
    (0 : ℝ) * clusterWeight = 0 := by
  simp

theorem external_probe_row_controls_touching_clusters
    {Γ P : Type*} [DecidableEq Γ]
    (clusters : Finset Γ)
    (p : P)
    (multiplicity : P → Γ → ℕ)
    (w : Γ → ℝ)
    (alpha : ℝ)
    (hw : ∀ γ ∈ clusters, 0 ≤ w γ)
    (hrow :
      (∑ γ ∈ clusters, (multiplicity p γ : ℝ) * w γ) ≤ alpha) :
    (∑ γ ∈ clusters,
      if 0 < multiplicity p γ then w γ else 0) ≤ alpha := by
  have hterm :
      ∀ γ ∈ clusters,
        (if 0 < multiplicity p γ then w γ else 0)
          ≤ (multiplicity p γ : ℝ) * w γ := by
    intro γ hγ
    by_cases htouch : 0 < multiplicity p γ
    · simp only [htouch, if_true]
      have hmNat : 1 ≤ multiplicity p γ := by omega
      have hm : (1 : ℝ) ≤ (multiplicity p γ : ℝ) := by
        exact_mod_cast hmNat
      nlinarith [hw γ hγ]
    · simp only [htouch, if_false]
      exact mul_nonneg (by positivity) (hw γ hγ)
  exact le_trans (Finset.sum_le_sum hterm) hrow

theorem cauchy_rows_give_fixed_recertification
    (M r g h beta : ℝ)
    (hr : 0 < r)
    (hg : g ≤ M / r)
    (hh : h ≤ 2 * M / r ^ 2)
    (hbeta : beta = (g + h) / 2) :
    beta ≤ M * (1 / (2 * r) + 1 / r ^ 2) := by
  rw [hbeta]
  calc
    (g + h) / 2 ≤ (M / r + 2 * M / r ^ 2) / 2 := by linarith
    _ = M * (1 / (2 * r) + 1 / r ^ 2) := by
      field_simp [ne_of_gt hr]

noncomputable def decayingCompactRow (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

noncomputable def growingRecertificationCost (n : ℕ) : ℝ :=
  (n : ℝ) + 1

theorem growingCost_mul_decayingRow (n : ℕ) :
    growingRecertificationCost n * decayingCompactRow n = 1 := by
  dsimp [growingRecertificationCost, decayingCompactRow]
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

theorem variable_recertification_can_destroy_subunit_admission
    (delta : ℝ) (hdelta : delta < 1) (n : ℕ) :
    ¬ growingRecertificationCost n * decayingCompactRow n < delta := by
  rw [growingCost_mul_decayingRow]
  linarith

#print axioms zero_activity_pinned_cluster_vanishes
#print axioms external_probe_row_controls_touching_clusters
#print axioms cauchy_rows_give_fixed_recertification
#print axioms growingCost_mul_decayingRow
#print axioms variable_recertification_can_destroy_subunit_admission

end Millennium.YangMills
