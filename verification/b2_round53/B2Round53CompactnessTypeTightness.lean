import Mathlib

namespace B2Round53

theorem rh_exact_solve_can_escape (M : ℝ) (hM : 0 ≤ M) :
    ∃ μ z : ℝ, 0 < μ ∧ μ * z = 1 ∧ M < z := by
  let z : ℝ := M + 1
  have hz : 0 < z := by dsimp [z]; linarith
  refine ⟨z⁻¹, z, inv_pos.mpr hz, ?_, ?_⟩
  · simp [ne_of_gt hz]
  · dsimp [z]; linarith

theorem pnp_shared_prefix_overcounts :
    let shared : Finset ℕ := Finset.range 4
    let s0 : Finset ℕ := insert 4 shared
    let s1 : Finset ℕ := insert 5 shared
    let s2 : Finset ℕ := insert 6 shared
    s0.card = 5 ∧ s1.card = 5 ∧ s2.card = 5 ∧
      s0.card + s1.card + s2.card = 15 ∧ (s0 ∪ s1 ∪ s2).card = 7 := by
  norm_num

theorem bsd_even_ledger_does_not_force_zero :
    ∃ lval h correction a b c : ℤ,
      lval = 2 * a ∧ h = 2 * b ∧ correction = 2 * c ∧
      lval = h + correction ∧ correction ≠ 0 := by
  refine ⟨4, 2, 2, 2, 1, 1, ?_⟩
  norm_num

theorem hodge_rational_factor_pair_outside_integer_list :
    let a : ℚ := 1 / 3
    let b : ℚ := 25 / 3
    (3 * a + 1) * (3 * b + 1) = 52 ∧
      a ≠ 0 ∧ a ≠ 17 ∧ a ≠ -1 ∧ a ≠ -9 ∧ a ≠ 1 ∧ a ≠ 4 := by
  norm_num

def nsPointMass (n k : ℕ) : ℕ := if k = n then 1 else 0

theorem ns_local_extinction_does_not_imply_global_extinction (R : ℕ) :
    ∃ n : ℕ, R < n ∧
      (∀ k : ℕ, k ≤ R → nsPointMass n k = 0) ∧ nsPointMass n n = 1 := by
  refine ⟨R + 1, by omega, ?_, ?_⟩
  · intro k hk
    have hne : k ≠ R + 1 := by omega
    simp [nsPointMass, hne]
  · simp [nsPointMass]

theorem ym_strict_contraction_can_have_small_physical_defect
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    let q : ℝ := 1 - a ^ 2
    0 < q ∧ q < 1 ∧ (1 - q) / a = a := by
  dsimp
  have hm : 0 < 1 - a := by linarith
  have hp : 0 < 1 + a := by linarith
  have hprod : 0 < (1 - a) * (1 + a) := mul_pos hm hp
  have ha2 : 0 < a * a := mul_pos ha ha
  constructor
  · nlinarith
  constructor
  · nlinarith
  · apply (div_eq_iff (ne_of_gt ha)).2
    ring

#print axioms rh_exact_solve_can_escape
#print axioms pnp_shared_prefix_overcounts
#print axioms bsd_even_ledger_does_not_force_zero
#print axioms hodge_rational_factor_pair_outside_integer_list
#print axioms ns_local_extinction_does_not_imply_global_extinction
#print axioms ym_strict_contraction_can_have_small_physical_defect

end B2Round53
