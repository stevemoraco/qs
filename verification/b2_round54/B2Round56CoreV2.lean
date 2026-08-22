import Mathlib

open scoped BigOperators

namespace B2Round56FactorizationOverlapEnergyFirewallsV2

theorem rh_one_shared_resource_cannot_encode_opposite_signs
    (a b v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ¬ (a * v = 1 ∧ b * v = -1) := by
  rintro ⟨hav, hbv⟩
  by_cases hv : 0 ≤ v
  · have hnonneg : 0 ≤ b * v := mul_nonneg hb hv
    rw [hbv] at hnonneg
    linarith
  · have hvle : v ≤ 0 := le_of_not_ge hv
    have hnonpos : a * v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hvle
    rw [hav] at hnonpos
    linarith

theorem pnp_three_disjoint_markers_cap_common_floor
    (p0 p1 p2 δ : ℝ)
    (_hp0 : 0 ≤ p0) (_hp1 : 0 ≤ p1) (_hp2 : 0 ≤ p2)
    (hsum : p0 + p1 + p2 = 1)
    (hδ : (1 : ℝ) / 3 < δ) :
    ¬ (δ ≤ p0 ∧ δ ≤ p1 ∧ δ ≤ p2) := by
  rintro ⟨h0, h1, h2⟩
  linarith

theorem bsd_unit_local_defects_have_unbounded_partial_total
    (B : ℕ) :
    ∃ N : ℕ, B < Finset.sum (Finset.range N) (fun _p => (1 : ℕ)) := by
  refine ⟨B + 1, ?_⟩
  simpa using Nat.lt_succ_self B

theorem hodge_center_family_survives_numeric_gates
    (b : ℤ) (hb : 2 ≤ b) :
    let c : ℤ := 4 * b + 13
    0 ≤ 2 * b - 4 ∧
    0 ≤ 8 * c - 116 ∧
    0 ≤ c + 4 * b - 29 ∧
    (c + 4 * b - 29) ^ 2 ≤ (2 * b - 4) * (8 * c - 116) := by
  dsimp
  constructor
  · omega
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem ns_fixed_determinant_does_not_bound_inverse_scale
    (B : ℚ) (hB : 0 ≤ B) :
    ∃ x y : ℚ,
      0 < x ∧ x * y = -1 ∧ y * (-x) = 1 ∧ B < |(-x)| := by
  let x : ℚ := B + 1
  let y : ℚ := -(1 / x)
  have hxpos : 0 < x := by
    dsimp [x]
    linarith
  have hxne : x ≠ 0 := ne_of_gt hxpos
  refine ⟨x, y, hxpos, ?_, ?_, ?_⟩
  · dsimp [y]
    field_simp [hxne]
  · dsimp [y]
    field_simp [hxne]
  · rw [abs_neg, abs_of_pos hxpos]
    dsimp [x]
    linarith

theorem ym_projection_can_raise_rayleigh_scale_arbitrarily
    (B : ℚ) (hB : 0 ≤ B) :
    let M : ℚ := 2 * (B + 1)
    let projectedNormSq : ℚ := 1 / 2
    let projectedEnergy : ℚ := M / 4
    0 < M ∧
    projectedEnergy / projectedNormSq = B + 1 ∧
    B < projectedEnergy / projectedNormSq := by
  dsimp
  constructor
  · linarith
  constructor
  · ring
  · linarith

#print axioms rh_one_shared_resource_cannot_encode_opposite_signs
#print axioms pnp_three_disjoint_markers_cap_common_floor
#print axioms bsd_unit_local_defects_have_unbounded_partial_total
#print axioms hodge_center_family_survives_numeric_gates
#print axioms ns_fixed_determinant_does_not_bound_inverse_scale
#print axioms ym_projection_can_raise_rayleigh_scale_arbitrarily

end B2Round56FactorizationOverlapEnergyFirewallsV2
