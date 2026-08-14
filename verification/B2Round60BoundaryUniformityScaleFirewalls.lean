import Mathlib

/-!
# B2 Round 60 — boundary, uniformity, and physical-scale firewalls

Finite scalar / quantifier countermodels only.  No declaration below states or
proves any official Millennium Prize problem.
-/

namespace B2Round60

/-- Strict positivity at every finite stage does not furnish any uniform positive
floor.  This is the scalar boundary of finite additive-margin transport. -/
theorem rh_strict_margin_survival_has_no_uniform_floor
    (c : ℝ) (hc : 0 < c) :
    ∃ reference reserve perturbed error : ℝ,
      0 < reserve ∧
      reserve ≤ reference ∧
      |perturbed - reference| ≤ error ∧
      error < reserve ∧
      0 < perturbed ∧
      perturbed < c := by
  refine ⟨c / 2, c / 2, c / 2, 0, ?_, le_rfl, ?_, ?_, ?_, ?_⟩
  · linarith
  · norm_num
  · linarith
  · linarith
  · linarith

/-- Every finite prefix can have a common witness while no single natural-number
witness handles all constraints.  Any infinite-family upgrade therefore needs a
compactness/tightness theorem, not just finite-family existence. -/
theorem pnp_finite_prefix_witnesses_do_not_give_global_witness :
    (∀ N : ℕ, ∃ x : ℕ, ∀ k : ℕ, k ≤ N → k ≤ x) ∧
    ¬ ∃ x : ℕ, ∀ k : ℕ, k ≤ x := by
  constructor
  · intro N
    exact ⟨N, fun k hk => hk⟩
  · rintro ⟨x, hx⟩
    have hbad := hx (x + 1)
    omega

/-- Exact control at one selected local index leaves another local index
arbitrarily large.  This is an abstract local-to-global firewall only. -/
theorem bsd_selected_local_control_leaves_other_index_unbounded
    (B : ℕ) :
    ∃ d : ℕ → ℕ, d 3 = 0 ∧ B < d 5 := by
  refine ⟨fun p => if p = 5 then B + 1 else 0, ?_, ?_⟩
  · simp
  · simp

/-- Exponent bookkeeping for one monomial with two distinct degree-nine square
factorizations:

`x^18 y^6 = (x^9)^2 y^6 = (x^8 y)^2 (x^2 y^4)`.

Thus degree data alone cannot identify a geometric conductor factor. -/
theorem hodge_degree_nine_square_factor_not_unique :
    ((18 : ℕ) + 6 = 24) ∧
    ((9 : ℕ) + 0 = 9) ∧
    ((0 : ℕ) + 6 = 6) ∧
    ((2 : ℕ) * 9 + 0 = 18) ∧
    ((2 : ℕ) * 0 + 6 = 6) ∧
    ((8 : ℕ) + 1 = 9) ∧
    ((2 : ℕ) + 4 = 6) ∧
    ((2 : ℕ) * 8 + 2 = 18) ∧
    ((2 : ℕ) * 1 + 4 = 6) ∧
    (9 : ℕ) ≠ 8 := by
  norm_num

/-- A constrained maximum on a one-sided admissible half-line need not have
zero first variation.  Here `F(s)=-s` is maximal at the boundary `s=0`, while
every right difference quotient is exactly `-1`. -/
theorem ns_one_sided_maximum_has_nonzero_right_variation :
    (∀ s : ℝ, 0 ≤ s → -s ≤ 0) ∧
    (∀ t : ℝ, 0 < t → (-t - 0) / t = -1) := by
  constructor
  · intro s hs
    linarith
  · intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    calc
      (-t - 0) / t = (-t) / t := by ring
      _ = -1 := by field_simp [ht0]

/-- If a lattice-step contraction base stays fixed away from one while the
physical step shrinks, the inferred physical decay rate can exceed any fixed
bound.  Therefore a continuum mass statement needs the base to scale with the
physical time step. -/
theorem ym_fixed_base_shrinking_step_has_unbounded_physical_rate
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ τ : ℝ, 0 < τ ∧
      B < -(Real.log (Real.exp (-1))) / τ := by
  have hpos : 0 < B + 1 := by linarith
  have hne : B + 1 ≠ 0 := ne_of_gt hpos
  refine ⟨1 / (B + 1), by positivity, ?_⟩
  have hrate :
      -(Real.log (Real.exp (-1))) / (1 / (B + 1)) = B + 1 := by
    rw [Real.log_exp]
    field_simp [hne]
  rw [hrate]
  linarith

#print axioms rh_strict_margin_survival_has_no_uniform_floor
#print axioms pnp_finite_prefix_witnesses_do_not_give_global_witness
#print axioms bsd_selected_local_control_leaves_other_index_unbounded
#print axioms hodge_degree_nine_square_factor_not_unique
#print axioms ns_one_sided_maximum_has_nonzero_right_variation
#print axioms ym_fixed_base_shrinking_step_has_unbounded_physical_rate

end B2Round60
