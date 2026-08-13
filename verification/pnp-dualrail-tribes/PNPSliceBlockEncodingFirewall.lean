import Mathlib

/-!
# P versus NP: fixed-slice safe block-encoding obstruction

Finite scalar and finite-set core only. This file does not define circuits,
monotone circuits, MCSP, Gap-MCSP, P, NP, or P versus NP.
-/

namespace PNP
namespace SliceBlockEncodingFirewall

/-- Safety of the three non-witness block pairs forces the encoded negative
weight to be at least the encoded positive weight when the negative source has
at least as many one-blocks as the positive source. -/
theorem safe_block_weight_monotone
    (M g h p0 p1 q0 q1 : ℝ)
    (hg0 : 0 ≤ g)
    (hgh : g ≤ h)
    (hhM : h ≤ M)
    (hp0q0 : p0 ≤ q0)
    (hp0q1 : p0 ≤ q1)
    (hp1q1 : p1 ≤ q1) :
    g * p1 + (M - g) * p0 ≤ h * q1 + (M - h) * q0 := by
  have hh0 : 0 ≤ h := le_trans hg0 hgh
  have hMh : 0 ≤ M - h := sub_nonneg.mpr hhM
  by_cases hp : p0 ≤ p1
  · have h1 : 0 ≤ h * (q1 - p1) :=
      mul_nonneg hh0 (sub_nonneg.mpr hp1q1)
    have h2 : 0 ≤ (M - h) * (q0 - p0) :=
      mul_nonneg hMh (sub_nonneg.mpr hp0q0)
    have h3 : 0 ≤ (h - g) * (p1 - p0) :=
      mul_nonneg (sub_nonneg.mpr hgh) (sub_nonneg.mpr hp)
    nlinarith
  · have hp' : p1 < p0 := lt_of_not_ge hp
    have h1 : 0 ≤ h * (q1 - p0) :=
      mul_nonneg hh0 (sub_nonneg.mpr hp0q1)
    have h2 : 0 ≤ (M - h) * (q0 - p0) :=
      mul_nonneg hMh (sub_nonneg.mpr hp0q0)
    have h3 : 0 ≤ g * (p0 - p1) :=
      mul_nonneg hg0 (sub_nonneg.mpr hp'.le)
    nlinarith

/-- In the strict source-weight case, equality of the encoded slice weights
forces the two positive-side block weights, and the positive-one/negative-one
block weights, to coincide. -/
theorem equal_slice_forces_block_weight_degeneracy
    (M g h p0 p1 q0 q1 : ℝ)
    (hg0 : 0 < g)
    (hgh : g < h)
    (hhM : h ≤ M)
    (hp0q0 : p0 ≤ q0)
    (hp0q1 : p0 ≤ q1)
    (hp1q1 : p1 ≤ q1)
    (heq : g * p1 + (M - g) * p0 =
      h * q1 + (M - h) * q0) :
    p0 = p1 ∧ p1 = q1 := by
  have hh0 : 0 < h := lt_trans hg0 hgh
  have hMh : 0 ≤ M - h := sub_nonneg.mpr hhM
  by_cases hp : p0 ≤ p1
  · have h1 : 0 ≤ h * (q1 - p1) :=
      mul_nonneg hh0.le (sub_nonneg.mpr hp1q1)
    have h2 : 0 ≤ (M - h) * (q0 - p0) :=
      mul_nonneg hMh (sub_nonneg.mpr hp0q0)
    have h3 : 0 ≤ (h - g) * (p1 - p0) :=
      mul_nonneg (sub_nonneg.mpr hgh.le) (sub_nonneg.mpr hp)
    have hsum :
        h * (q1 - p1) + (M - h) * (q0 - p0) +
          (h - g) * (p1 - p0) = 0 := by
      nlinarith
    have hz3 : (h - g) * (p1 - p0) = 0 := by
      nlinarith
    have hpEq : p1 = p0 := by
      have hnonzero : h - g ≠ 0 := ne_of_gt (sub_pos.mpr hgh)
      have : p1 - p0 = 0 := (mul_eq_zero.mp hz3).resolve_left hnonzero
      linarith
    have hz1 : h * (q1 - p1) = 0 := by
      nlinarith
    have hqEq : q1 = p1 := by
      have hnonzero : h ≠ 0 := ne_of_gt hh0
      have : q1 - p1 = 0 := (mul_eq_zero.mp hz1).resolve_left hnonzero
      linarith
    exact ⟨hpEq.symm, hqEq.symm⟩
  · have hp' : p1 < p0 := lt_of_not_ge hp
    have h1 : 0 ≤ h * (q1 - p0) :=
      mul_nonneg hh0.le (sub_nonneg.mpr hp0q1)
    have h2 : 0 ≤ (M - h) * (q0 - p0) :=
      mul_nonneg hMh (sub_nonneg.mpr hp0q0)
    have h3 : 0 < g * (p0 - p1) :=
      mul_pos hg0 (sub_pos.mpr hp')
    exfalso
    nlinarith

variable {Ω : Type*} [DecidableEq Ω]

/-- A finite subset with the same cardinality as its superset is equal to it. -/
theorem finset_eq_of_subset_of_card_eq
    {A B : Finset Ω} (hsub : A ⊆ B) (hcard : A.card = B.card) : A = B := by
  apply Finset.Subset.antisymm hsub
  intro x hx
  by_contra hxA
  have hinsert : insert x A ⊆ B := by
    intro y hy
    simp only [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hx
    · exact hsub hy
  have hcardLe := Finset.card_le_card hinsert
  simp [hxA, hcard] at hcardLe

/-- If the safety inclusions hold and the relevant block cardinalities are all
equal, the valid positive-one/negative-zero witness fiber is empty. -/
theorem equal_safe_blocks_have_no_valid_witness
    (P0 P1 Q0 Q1 : Finset Ω)
    (hP0Q0 : P0 ⊆ Q0)
    (hP0Q1 : P0 ⊆ Q1)
    (hP1Q1 : P1 ⊆ Q1)
    (hP : P0.card = P1.card)
    (hQ : P1.card = Q1.card) :
    ¬ ∃ x, x ∈ P1 ∧ x ∉ Q0 := by
  have hP0Q1card : P0.card = Q1.card := hP.trans hQ
  have hP0eqQ1 : P0 = Q1 :=
    finset_eq_of_subset_of_card_eq hP0Q1 hP0Q1card
  have hP1eqQ1 : P1 = Q1 :=
    finset_eq_of_subset_of_card_eq hP1Q1 hQ
  rintro ⟨x, hxP1, hxQ0⟩
  have hxQ1 : x ∈ Q1 := by simpa [hP1eqQ1] using hxP1
  have hxP0 : x ∈ P0 := by simpa [hP0eqQ1] using hxQ1
  exact hxQ0 (hP0Q0 hxP0)

/-- Real-valued total weight of a uniform block encoding. -/
def blockWeight
    (M ones : ℕ) (zeroBlock oneBlock : Finset Ω) : ℝ :=
  (ones : ℝ) * (oneBlock.card : ℝ) +
    ((M : ℝ) - ones) * (zeroBlock.card : ℝ)

/-- A safe coordinatewise block encoding of a strictly heavier negative source
cannot place both encoded sides on one equal-weight slice while retaining a
valid `positive-one -> negative-zero` witness coordinate. -/
theorem strict_weight_safe_equal_slice_has_no_witness
    (M g h : ℕ)
    (P0 P1 Q0 Q1 : Finset Ω)
    (hg0 : 0 < g)
    (hgh : g < h)
    (hhM : h ≤ M)
    (hP0Q0 : P0 ⊆ Q0)
    (hP0Q1 : P0 ⊆ Q1)
    (hP1Q1 : P1 ⊆ Q1)
    (heq : blockWeight M g P0 P1 = blockWeight M h Q0 Q1) :
    ¬ ∃ x, x ∈ P1 ∧ x ∉ Q0 := by
  have hscalar := equal_slice_forces_block_weight_degeneracy
    (M : ℝ) (g : ℝ) (h : ℝ)
    (P0.card : ℝ) (P1.card : ℝ) (Q0.card : ℝ) (Q1.card : ℝ)
    (by exact_mod_cast hg0)
    (by exact_mod_cast hgh)
    (by exact_mod_cast hhM)
    (by exact_mod_cast Finset.card_le_card hP0Q0)
    (by exact_mod_cast Finset.card_le_card hP0Q1)
    (by exact_mod_cast Finset.card_le_card hP1Q1)
    (by simpa [blockWeight] using heq)
  have hP : P0.card = P1.card := by exact_mod_cast hscalar.1
  have hQ : P1.card = Q1.card := by exact_mod_cast hscalar.2
  exact equal_safe_blocks_have_no_valid_witness
    P0 P1 Q0 Q1 hP0Q0 hP0Q1 hP1Q1 hP hQ

#print axioms safe_block_weight_monotone
#print axioms equal_slice_forces_block_weight_degeneracy
#print axioms finset_eq_of_subset_of_card_eq
#print axioms equal_safe_blocks_have_no_valid_witness
#print axioms strict_weight_safe_equal_slice_has_no_witness

end SliceBlockEncodingFirewall
end PNP
