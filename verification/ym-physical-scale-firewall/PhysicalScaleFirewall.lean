import Mathlib

/-!
# Yang--Mills physical-scale firewall

Finite scalar countermodel only; not Yang--Mills or an OS reconstruction.

A regulator family can have uniformly positive equal-time variance, arbitrarily
strong uniform clustering in lattice-step distance, and a fixed positive
lattice-unit gap `a_n M_n = 1`, while its physical mass scale escapes to
infinity and its correlation at one fixed physical unit of separation is zero.

Therefore equal-time noncollapse plus an upper clustering estimate does not by
itself provide the finite-physical-energy tightness required in a continuum
mass-gap construction.
-/

namespace Millennium.YangMills.PhysicalScaleFirewall

noncomputable def spacing (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

noncomputable def physicalMass (n : ℕ) : ℝ := (n : ℝ) + 1

def corr (_n k : ℕ) : ℝ := if k = 0 then 1 else 0

theorem equal_time_variance_one (n : ℕ) : corr n 0 = 1 := by
  simp [corr]

theorem positive_step_correlation_zero (n k : ℕ) (hk : 0 < k) :
    corr n k = 0 := by
  simp [corr, Nat.ne_of_gt hk]

theorem geometric_clustering
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ n k : ℕ, |corr n k| ≤ q ^ k := by
  intro n k
  by_cases hk : k = 0
  · subst k
    simp [corr]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    rw [positive_step_correlation_zero n k hkpos]
    simp only [abs_zero]
    exact pow_nonneg hq k

theorem spacing_pos (n : ℕ) : 0 < spacing n := by
  unfold spacing
  positivity

theorem fixed_dimensionless_gap (n : ℕ) :
    spacing n * physicalMass n = 1 := by
  unfold spacing physicalMass
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hne]

theorem unit_physical_separation (n : ℕ) :
    spacing n * ((n : ℝ) + 1) = 1 := by
  simpa [physicalMass] using fixed_dimensionless_gap n

theorem correlation_at_unit_physical_separation_zero (n : ℕ) :
    corr n (n + 1) = 0 := by
  apply positive_step_correlation_zero
  omega

theorem physical_mass_unbounded :
    ∀ C : ℝ, ∃ n : ℕ, C < physicalMass n := by
  intro C
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine ⟨n, ?_⟩
  unfold physicalMass
  linarith

theorem variance_clustering_do_not_prevent_physical_spectral_escape :
    (∀ n : ℕ, corr n 0 = 1) ∧
    (∀ n k : ℕ, |corr n k| ≤ ((1 : ℝ) / 2) ^ k) ∧
    (∀ n : ℕ, spacing n * physicalMass n = 1) ∧
    (∀ C : ℝ, ∃ n : ℕ, C < physicalMass n) ∧
    (∀ n : ℕ, corr n (n + 1) = 0) := by
  refine ⟨equal_time_variance_one, ?_, fixed_dimensionless_gap,
    physical_mass_unbounded, correlation_at_unit_physical_separation_zero⟩
  exact geometric_clustering ((1 : ℝ) / 2) (by norm_num)

#print axioms equal_time_variance_one
#print axioms positive_step_correlation_zero
#print axioms geometric_clustering
#print axioms spacing_pos
#print axioms fixed_dimensionless_gap
#print axioms unit_physical_separation
#print axioms correlation_at_unit_physical_separation_zero
#print axioms physical_mass_unbounded
#print axioms variance_clustering_do_not_prevent_physical_spectral_escape

end Millennium.YangMills.PhysicalScaleFirewall
