import Mathlib

namespace B4Auto17Run10.RH

theorem same_first_moment_different_second_moment :
    ((0 : ℤ) + (-4) = (-1) + (-3)) ∧
      ((0 : ℤ)^2 + (-4)^2 ≠ (-1)^2 + (-3)^2) := by
  norm_num

theorem first_moment_does_not_identify_second :
    ∃ a b c d : ℤ,
      a + b = c + d ∧ a^2 + b^2 ≠ c^2 + d^2 := by
  refine ⟨0, -4, -1, -3, ?_⟩
  norm_num

theorem exact_second_moment_match_closes_residual
    (target observed : ℤ) (h : observed = target) :
    target - observed = 0 := by
  omega

#print axioms same_first_moment_different_second_moment
#print axioms first_moment_does_not_identify_second
#print axioms exact_second_moment_match_closes_residual

end B4Auto17Run10.RH

namespace B4Auto17Run10.PNP

def fails (d x : Bool) : Prop := d = x

theorem every_fixed_decoder_has_bad_input :
    ∀ d : Bool, ∃ x : Bool, fails d x := by
  intro d
  exact ⟨d, rfl⟩

theorem no_universal_bad_input :
    ¬ (∃ x : Bool, ∀ d : Bool, fails d x) := by
  rintro ⟨x, hx⟩
  cases x with
  | false =>
      have h := hx true
      simp [fails] at h
  | true =>
      have h := hx false
      simp [fails] at h

theorem uniform_bad_input_closes_fixed_family
    {D X : Type} (fails' : D → X → Prop) (x : X)
    (hx : ∀ d : D, fails' d x) :
    ∃ x : X, ∀ d : D, fails' d x := by
  exact ⟨x, hx⟩

#print axioms every_fixed_decoder_has_bad_input
#print axioms no_universal_bad_input
#print axioms uniform_bad_input_closes_fixed_family

end B4Auto17Run10.PNP

namespace B4Auto17Run10.BSD

theorem one_coordinate_audit_nonidentifiable :
    let a : Nat × Nat := (1, 0)
    let b : Nat × Nat := (1, 1)
    a.1 = b.1 ∧ a ≠ b := by
  norm_num

theorem full_pair_audit_identifies
    (a b : Nat × Nat)
    (h₁ : a.1 = b.1) (h₂ : a.2 = b.2) :
    a = b := by
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  simp_all

theorem omitted_positive_local_defect_breaks_exact_equality
    (known omitted : Nat) (h : 0 < omitted) :
    known < known + omitted := by
  omega

theorem exact_global_equality_forces_omitted_zero
    (known omitted : Nat)
    (h : known + omitted = known) :
    omitted = 0 := by
  omega

#print axioms one_coordinate_audit_nonidentifiable
#print axioms full_pair_audit_identifies
#print axioms omitted_positive_local_defect_breaks_exact_equality
#print axioms exact_global_equality_forces_omitted_zero

end B4Auto17Run10.BSD

namespace B4Auto17Run10.Hodge

def Alg (z : ℤ) : Prop := ∃ k : ℤ, z = 2 * k

theorem algebraic_summands_give_algebraic_sum
    (x y : ℤ) (hx : Alg x) (hy : Alg y) :
    Alg (x + y) := by
  rcases hx with ⟨a, ha⟩
  rcases hy with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  omega

theorem algebraic_sum_can_hide_nonalgebraic_summands :
    Alg ((1 : ℤ) + 1) ∧ ¬ Alg (1 : ℤ) := by
  constructor
  · exact ⟨1, by norm_num⟩
  · intro h
    rcases h with ⟨k, hk⟩
    omega

theorem algebraic_sum_and_one_summand_recover_other
    (x y : ℤ) (hsum : Alg (x + y)) (hx : Alg x) :
    Alg y := by
  rcases hsum with ⟨s, hs⟩
  rcases hx with ⟨a, ha⟩
  refine ⟨s - a, ?_⟩
  omega

#print axioms algebraic_summands_give_algebraic_sum
#print axioms algebraic_sum_can_hide_nonalgebraic_summands
#print axioms algebraic_sum_and_one_summand_recover_other

end B4Auto17Run10.Hodge

namespace B4Auto17Run10.NavierStokes

theorem uniform_episode_cost_budget
    (N E c : ℝ) (hc : 0 < c) (hbudget : N * c ≤ E) :
    N ≤ E / c := by
  exact (le_div_iff₀ hc).2 hbudget

theorem positive_cost_alone_allows_arbitrary_counts (k : ℕ) :
    let n : ℝ := ((k + 1 : ℕ) : ℝ)
    let c : ℝ := 1 / n
    0 < c ∧ (k : ℝ) < n ∧ n * c = 1 := by
  dsimp
  have hn : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    positivity
  constructor
  · positivity
  constructor
  · exact_mod_cast Nat.lt_succ_self k
  · field_simp

theorem uniform_cost_floor_closes_count
    (N E c c₀ : ℝ)
    (hN : 0 ≤ N) (hc₀ : 0 < c₀)
    (hfloor : c₀ ≤ c) (hbudget : N * c ≤ E) :
    N ≤ E / c₀ := by
  apply (le_div_iff₀ hc₀).2
  have hmul : N * c₀ ≤ N * c := by
    exact mul_le_mul_of_nonneg_left hfloor hN
  linarith

#print axioms uniform_episode_cost_budget
#print axioms positive_cost_alone_allows_arbitrary_counts
#print axioms uniform_cost_floor_closes_count

end B4Auto17Run10.NavierStokes

namespace B4Auto17Run10.YangMills

theorem scaled_lower_bound_transfers
    (a m g : ℝ) (ha : 0 < a) (h : a * m ≤ g) :
    m ≤ g / a := by
  apply (le_div_iff₀ ha).2
  nlinarith

theorem scaled_error_margin_transfers
    (a m eps g : ℝ)
    (ha : 0 < a) (hmargin : eps < m)
    (happrox : a * m - a * eps ≤ g) :
    0 < g ∧ m - eps ≤ g / a := by
  constructor
  · have hpos : 0 < a * (m - eps) := by
      exact mul_pos ha (sub_pos.mpr hmargin)
    nlinarith
  · apply (le_div_iff₀ ha).2
    nlinarith

theorem quadratic_lattice_gap_has_physical_value_a
    (a : ℝ) (ha : 0 < a) :
    (a * a) / a = a := by
  field_simp [ne_of_gt ha]

theorem positive_lattice_gap_does_not_supply_fixed_physical_margin :
    let a : ℝ := 1 / 100
    let g : ℝ := a * a
    0 < g ∧ g / a = 1 / 100 ∧ g / a < 1 / 10 := by
  norm_num

#print axioms scaled_lower_bound_transfers
#print axioms scaled_error_margin_transfers
#print axioms quadratic_lattice_gap_has_physical_value_a
#print axioms positive_lattice_gap_does_not_supply_fixed_physical_margin

end B4Auto17Run10.YangMills
