import Mathlib

namespace B4.Run22.Gauge

theorem banker_physical_gap_from_scale_cap {g mu a A : ℝ}
    (hmu : 0 < mu) (hg : mu ≤ g) (ha : 0 < a) (hcap : a ≤ A) :
    0 < A ∧ mu / A ≤ g / a := by
  have hA : 0 < A := lt_of_lt_of_le ha hcap
  have hg0 : 0 ≤ g := le_trans (le_of_lt hmu) hg
  constructor
  · exact hA
  · rw [div_le_div_iff₀ hA ha]
    have h1 : mu * a ≤ g * a :=
      mul_le_mul_of_nonneg_right hg (le_of_lt ha)
    have h2 : g * a ≤ g * A :=
      mul_le_mul_of_nonneg_left hcap hg0
    exact le_trans h1 h2

theorem critic_positive_dimensionless_gap_can_collapse_physically :
    ∃ g a eps : ℝ,
      0 < g ∧ 0 < a ∧ 0 < eps ∧ g / a < eps := by
  exact ⟨1, 1000, 1 / 100, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem cleaner_physical_gap_with_error_reserve {g gK delta mu a A : ℝ}
    (hmu : 0 < mu) (hreserve : mu + delta ≤ gK)
    (hexact : gK - delta ≤ g) (ha : 0 < a) (hcap : a ≤ A) :
    mu / A ≤ g / a := by
  have hmuG : mu ≤ g := by linarith
  exact (banker_physical_gap_from_scale_cap hmu hmuG ha hcap).2

#print axioms banker_physical_gap_from_scale_cap
#print axioms critic_positive_dimensionless_gap_can_collapse_physically
#print axioms cleaner_physical_gap_with_error_reserve

end B4.Run22.Gauge
