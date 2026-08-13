import Mathlib
open scoped BigOperators
namespace B2Round56Core

theorem rh_opposite_signs
    (a b v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ¬ (a * v = 1 ∧ b * v = -1) := by
  rintro ⟨hav, hbv⟩
  by_cases hv : 0 ≤ v
  · have h : 0 ≤ b * v := mul_nonneg hb hv
    rw [hbv] at h
    linarith
  · have hvle : v ≤ 0 := le_of_not_ge hv
    have h : a * v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hvle
    rw [hav] at h
    linarith

theorem pnp_disjoint_floor
    (p0 p1 p2 δ : ℝ)
    (hsum : p0 + p1 + p2 = 1)
    (hδ : (1 : ℝ) / 3 < δ) :
    ¬ (δ ≤ p0 ∧ δ ≤ p1 ∧ δ ≤ p2) := by
  rintro ⟨h0, h1, h2⟩
  linarith

theorem bsd_unbounded_partial_total (B : ℕ) :
    ∃ N : ℕ, B < ∑ _p in Finset.range N, (1 : ℕ) := by
  refine ⟨B + 1, ?_⟩
  simpa using Nat.lt_succ_self B

theorem hodge_center_family
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

theorem ns_det_not_inverse
    (B : ℚ) (hB : 0 ≤ B) :
    ∃ x y : ℚ,
      0 < x ∧ x * y = -1 ∧ y * (-x) = 1 ∧ B < |(-x)| := by
  let x : ℚ := B + 1
  let y : ℚ := -(1 / x)
  have hxpos : 0 < x := by dsimp [x]; linarith
  have hxne : x ≠ 0 := ne_of_gt hxpos
  refine ⟨x, y, hxpos, ?_, ?_, ?_⟩
  · dsimp [y]
    field_simp [hxne]
  · dsimp [y]
    field_simp [hxne]
  · rw [abs_neg, abs_of_pos hxpos]
    dsimp [x]
    linarith

theorem ym_projection_energy
    (B : ℚ) (hB : 0 ≤ B) :
    let M : ℚ := 2 * (B + 1)
    let n2 : ℚ := 1 / 2
    let e : ℚ := M / 4
    0 < M ∧ e / n2 = B + 1 ∧ B < e / n2 := by
  dsimp
  constructor
  · linarith
  constructor
  · ring
  · linarith

#print axioms rh_opposite_signs
#print axioms pnp_disjoint_floor
#print axioms bsd_unbounded_partial_total
#print axioms hodge_center_family
#print axioms ns_det_not_inverse
#print axioms ym_projection_energy
end B2Round56Core
