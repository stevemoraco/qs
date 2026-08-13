import Mathlib

namespace B2Round50

theorem hodge_two_invertible_with_nonzero_zero_divisors :
    ∃ (A B half : ℚ × ℚ),
      (2 : ℚ × ℚ) * half = 1 ∧ A ≠ 0 ∧ B ≠ 0 ∧ B * A = 0 := by
  refine ⟨((1 : ℚ), 0), (0, (1 : ℚ)), ((1 / 2 : ℚ), (1 / 2 : ℚ)), ?_, ?_, ?_, ?_⟩
  · ext <;> norm_num
  · norm_num
  · norm_num
  · ext <;> norm_num

theorem positive_pointwise_no_uniform_floor
    (c : ℝ) (hc : 0 < c) :
    ∃ j : ℝ, 0 < j ∧ j < c := by
  refine ⟨c / 2, ?_, ?_⟩ <;> linarith

theorem ns_nonzero_jacobian_does_not_give_uniform_transversality
    (c : ℝ) (hc : 0 < c) :
    ∃ jac : ℝ, jac ≠ 0 ∧ |jac| < c := by
  obtain ⟨jac, hjac, hsmall⟩ := positive_pointwise_no_uniform_floor c hc
  refine ⟨jac, ne_of_gt hjac, ?_⟩
  rw [abs_of_pos hjac]
  exact hsmall

theorem rh_positive_coefficients_do_not_give_uniform_coercivity
    (c : ℝ) (hc : 0 < c) :
    ∃ eps : ℝ, 0 < eps ∧ eps < c :=
  positive_pointwise_no_uniform_floor c hc

def bsdLocalPart (n : ℕ) : Set ℕ := {n}

theorem bsd_each_local_part_finite (n : ℕ) :
    (bsdLocalPart n).Finite := by
  simp [bsdLocalPart]

theorem bsd_all_local_parts_can_have_infinite_union :
    ¬ (⋃ n : ℕ, bsdLocalPart n).Finite := by
  have hUnion : (⋃ n : ℕ, bsdLocalPart n) = Set.univ := by
    ext x
    simp [bsdLocalPart]
  rw [hUnion]
  exact Set.infinite_univ

theorem pnp_local_charges_can_completely_merge (n : ℕ) :
    (∑ _ : Fin n, (1 : ℕ)) = n ∧ Fintype.card Unit = 1 := by
  simp

theorem ym_exact_gap_location_no_overlap_floor
    (Lambda delta : ℝ) (hLambda : 0 < Lambda) (hdelta : 0 < delta) :
    ∃ gamma weight : ℝ,
      gamma = Lambda ∧ 0 < gamma ∧ 0 < weight ∧ weight < delta := by
  refine ⟨Lambda, delta / 2, rfl, hLambda, ?_, ?_⟩ <;> linarith

#print axioms hodge_two_invertible_with_nonzero_zero_divisors
#print axioms positive_pointwise_no_uniform_floor
#print axioms ns_nonzero_jacobian_does_not_give_uniform_transversality
#print axioms rh_positive_coefficients_do_not_give_uniform_coercivity
#print axioms bsd_each_local_part_finite
#print axioms bsd_all_local_parts_can_have_infinite_union
#print axioms pnp_local_charges_can_completely_merge
#print axioms ym_exact_gap_location_no_overlap_floor

end B2Round50
