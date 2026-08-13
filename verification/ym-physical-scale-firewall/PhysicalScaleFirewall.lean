import Mathlib

namespace Millennium.YangMills.PhysicalScaleFirewall

noncomputable def spacing (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
noncomputable def physicalMass (n : ℕ) : ℝ := (n : ℝ) + 1
def corr (_n k : ℕ) : ℝ := if k = 0 then 1 else 0

theorem equal_time_variance_one (n : ℕ) : corr n 0 = 1 := by simp [corr]

theorem positive_step_correlation_zero (n k : ℕ) (hk : 0 < k) : corr n k = 0 := by
  simp [corr, Nat.ne_of_gt hk]

theorem geometric_clustering (q : ℝ) (hq : 0 ≤ q) : ∀ n k : ℕ, |corr n k| ≤ q ^ k := by
  intro n k
  by_cases hk : k = 0
  · subst k; simp [corr]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    rw [positive_step_correlation_zero n k hkpos]
    exact pow_nonneg hq k

theorem spacing_pos (n : ℕ) : 0 < spacing n := by unfold spacing; positivity

theorem fixed_dimensionless_gap (n : ℕ) : spacing n * physicalMass n = 1 := by
  unfold spacing physicalMass
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hne]

theorem unit_physical_separation (n : ℕ) : spacing n * ((n : ℝ) + 1) = 1 := by
  simpa [physicalMass] using fixed_dimensionless_gap n

theorem correlation_at_unit_physical_separation_zero (n : ℕ) : corr n (n + 1) = 0 := by
  apply positive_step_correlation_zero
  omega

theorem physical_mass_unbounded : ∀ C : ℝ, ∃ n : ℕ, C < physicalMass n := by
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
  refine ⟨equal_time_variance_one, ?_, fixed_dimensionless_gap, physical_mass_unbounded,
    correlation_at_unit_physical_separation_zero⟩
  exact geometric_clustering ((1 : ℝ) / 2) (by norm_num)

theorem high_mass_at_most_half_of_defect_budget
    {V high D a K : ℝ} (ha : 0 < a) (hK : 0 < K)
    (h1 : 2 * K * a * high ≤ D) (h2 : D ≤ K * a * V) : high ≤ V / 2 := by
  have hka : 0 < K * a := mul_pos hK ha
  have h : (K * a) * (2 * high) ≤ (K * a) * V := by
    calc
      (K * a) * (2 * high) = 2 * K * a * high := by ring
      _ ≤ D := h1
      _ ≤ K * a * V := h2
      _ = (K * a) * V := by ring
  have h3 : 2 * high ≤ V := (mul_le_mul_left hka).mp h
  linarith

theorem low_mass_positive_of_defect_budget
    {V low high D a K v : ℝ} (ha : 0 < a) (hK : 0 < K) (hv : 0 < v)
    (hV : v ≤ V) (hsplit : V = low + high)
    (h1 : 2 * K * a * high ≤ D) (h2 : D ≤ K * a * V) : v / 2 ≤ low := by
  have hh := high_mass_at_most_half_of_defect_budget ha hK h1 h2
  linarith

#print axioms equal_time_variance_one
#print axioms positive_step_correlation_zero
#print axioms geometric_clustering
#print axioms spacing_pos
#print axioms fixed_dimensionless_gap
#print axioms unit_physical_separation
#print axioms correlation_at_unit_physical_separation_zero
#print axioms physical_mass_unbounded
#print axioms variance_clustering_do_not_prevent_physical_spectral_escape
#print axioms high_mass_at_most_half_of_defect_budget
#print axioms low_mass_positive_of_defect_budget

end Millennium.YangMills.PhysicalScaleFirewall
