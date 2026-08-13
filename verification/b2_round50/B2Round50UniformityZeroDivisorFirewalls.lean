import Mathlib

/-!
# B2 round 50: uniformity, zero-divisor, and survival firewalls

Finite/logical/algebraic countermodels only.  No Millennium conclusion is
asserted here.
-/

namespace B2Round50

/-- Hodge first-jet firewall: a ring can have an explicit inverse for `2` and
still have nonzero zero divisors.  Thus equations `B i * A j = 0` do not by
themselves force either factor family to vanish. -/
theorem hodge_two_invertible_with_nonzero_zero_divisors :
    ∃ (A B half : ℚ × ℚ),
      (2 : ℚ × ℚ) * half = 1 ∧
      A ≠ 0 ∧ B ≠ 0 ∧ B * A = 0 := by
  refine ⟨((1 : ℚ), 0), (0, (1 : ℚ)), ((1 / 2 : ℚ), (1 / 2 : ℚ)), ?_⟩
  norm_num

/-- Generic scale firewall: pointwise positivity does not supply any positive
uniform lower bound. -/
theorem positive_pointwise_no_uniform_floor
    (c : ℝ) (hc : 0 < c) :
    ∃ j : ℝ, 0 < j ∧ j < c := by
  refine ⟨c / 2, ?_, ?_⟩ <;> linarith

/-- Navier--Stokes/AO specialization: a regenerated Jacobian determinant can be
nonzero at every tested scale while its quantitative transversality margin is
arbitrarily smaller than any proposed positive floor. -/
theorem ns_nonzero_jacobian_does_not_give_uniform_transversality
    (c : ℝ) (hc : 0 < c) :
    ∃ jac : ℝ, jac ≠ 0 ∧ |jac| < c := by
  obtain ⟨jac, hjac, hsmall⟩ := positive_pointwise_no_uniform_floor c hc
  refine ⟨jac, ne_of_gt hjac, ?_⟩
  rw [abs_of_pos hjac]
  exact hsmall

/-- RH operator specialization: pointwise positive quadratic coefficients do
not yield a scale-uniform coercivity constant. -/
theorem rh_positive_coefficients_do_not_give_uniform_coercivity
    (c : ℝ) (hc : 0 < c) :
    ∃ eps : ℝ, 0 < eps ∧ eps < c :=
  positive_pointwise_no_uniform_floor c hc

/-- A model for prime-local information: each local component is finite. -/
def bsdLocalPart (n : ℕ) : Set ℕ := {n}

theorem bsd_each_local_part_finite (n : ℕ) :
    (bsdLocalPart n).Finite := by
  simp [bsdLocalPart]

/-- ...but the union of all finite local components can still be infinite.
This is the finite-support firewall behind fixed-prime-to-global Sha upgrades. -/
theorem bsd_all_local_parts_can_have_infinite_union :
    ¬ (⋃ n : ℕ, bsdLocalPart n).Finite := by
  have hUnion : (⋃ n : ℕ, bsdLocalPart n) = Set.univ := by
    ext x
    simp [bsdLocalPart]
  rw [hUnion]
  exact Set.infinite_univ

/-- P-vs-NP anti-merging firewall: one unit local charge per requirement can
sum to `n`, while all requirements can point to the same single global resource.
A lower bound that sums local charges therefore needs a bounded-congestion or
distinctness theorem. -/
theorem pnp_local_charges_can_completely_merge (n : ℕ) :
    (∑ _ : Fin n, (1 : ℕ)) = n ∧ Fintype.card Unit = 1 := by
  simp

/-- Yang--Mills spectral-survival firewall: even exact placement of a candidate
exponent at `Lambda` is compatible with an arbitrarily small positive overlap
weight.  A continuum survival theorem therefore needs a nonvanishing projected
spectral weight (or equivalent physical-sector compactness), not only a gap
location estimate. -/
theorem ym_exact_gap_location_no_overlap_floor
    (Lambda delta : ℝ) (hLambda : 0 < Lambda) (hdelta : 0 < delta) :
    ∃ gamma weight : ℝ,
      gamma = Lambda ∧ 0 < weight ∧ weight < delta := by
  refine ⟨Lambda, delta / 2, rfl, ?_, ?_⟩ <;> linarith

#print axioms hodge_two_invertible_with_nonzero_zero_divisors
#print axioms positive_pointwise_no_uniform_floor
#print axioms ns_nonzero_jacobian_does_not_give_uniform_transversality
#print axioms rh_positive_coefficients_do_not_give_uniform_coercivity
#print axioms bsd_each_local_part_finite
#print axioms bsd_all_local_parts_can_have_infinite_union
#print axioms pnp_local_charges_can_completely_merge
#print axioms ym_exact_gap_location_no_overlap_floor

end B2Round50
