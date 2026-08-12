import Mathlib

namespace B4Auto18Run8.RH

theorem same_sum_second_moment_iff_same_product
    (a b c d : ℤ) (hsum : a + b = c + d) :
    a^2 + b^2 = c^2 + d^2 ↔ a * b = c * d := by
  constructor
  · intro hsq
    nlinarith [sq_nonneg (a + b), sq_nonneg (c + d)]
  · intro hprod
    nlinarith [sq_nonneg (a + b), sq_nonneg (c + d)]

theorem same_sum_does_not_force_same_product :
    ((0 : ℤ) + (-4) = (-1) + (-3)) ∧
      ((0 : ℤ) * (-4) ≠ (-1) * (-3)) := by
  norm_num

theorem same_sum_and_product_close_second_moment
    (a b c d : ℤ)
    (hsum : a + b = c + d) (hprod : a * b = c * d) :
    a^2 + b^2 = c^2 + d^2 := by
  exact (same_sum_second_moment_iff_same_product a b c d hsum).2 hprod

#print axioms same_sum_second_moment_iff_same_product
#print axioms same_sum_does_not_force_same_product
#print axioms same_sum_and_product_close_second_moment

end B4Auto18Run8.RH

namespace B4Auto18Run8.PNP

def solves (d x : Bool) : Prop := d = x

theorem no_fixed_decoder_solves_all :
    ∀ d : Bool, ¬ (∀ x : Bool, solves d x) := by
  intro d h
  cases d with
  | false =>
      have hf := h true
      simp [solves] at hf
  | true =>
      have ht := h false
      simp [solves] at ht

theorem input_dependent_selector_solves_all :
    ∀ x : Bool, solves x x := by
  intro x
  rfl

theorem constant_selector_recovers_fixed_decoder
    {D X : Type} (solves' : D → X → Prop)
    (sel : X → D) (d0 : D)
    (hconst : ∀ x, sel x = d0)
    (hsolve : ∀ x, solves' (sel x) x) :
    ∀ x, solves' d0 x := by
  intro x
  simpa [hconst x] using hsolve x

#print axioms no_fixed_decoder_solves_all
#print axioms input_dependent_selector_solves_all
#print axioms constant_selector_recovers_fixed_decoder

end B4Auto18Run8.PNP

namespace B4Auto18Run8.BSD

theorem zero_known_factor_hides_omitted_factor :
    ((0 : ℚ) * 2 = 0) ∧ ((2 : ℚ) ≠ 1) := by
  norm_num

theorem nonzero_known_factor_identifies_omitted_factor
    (known omitted : ℚ)
    (hknown : known ≠ 0)
    (hglobal : known * omitted = known) :
    omitted = 1 := by
  have hz : known * (omitted - 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hz with hk | ho
  · exact (hknown hk).elim
  · linarith

theorem positive_omitted_factor_changes_global_product
    (known omitted : ℚ)
    (hknown : 0 < known) (homitted : 1 < omitted) :
    known < known * omitted := by
  have hp : 0 < known * (omitted - 1) :=
    mul_pos hknown (sub_pos.mpr homitted)
  nlinarith

#print axioms zero_known_factor_hides_omitted_factor
#print axioms nonzero_known_factor_identifies_omitted_factor
#print axioms positive_omitted_factor_changes_global_product

end B4Auto18Run8.BSD

namespace B4Auto18Run8.Hodge

theorem retract_transfers_property
    {X Y : Type}
    (AlgX : X → Prop) (AlgY : Y → Prop)
    (i : X → Y) (r : Y → X) (x : X)
    (hretract : r (i x) = x)
    (hpreserve : ∀ y, AlgY y → AlgX (r y))
    (hupstairs : AlgY (i x)) :
    AlgX x := by
  rw [← hretract]
  exact hpreserve (i x) hupstairs

theorem retract_without_property_preservation_counterexample :
    let AlgX : Bool → Prop := fun b => b = false
    let AlgY : Bool → Prop := fun _ => True
    let i : Bool → Bool := id
    let r : Bool → Bool := id
    r (i true) = true ∧ AlgY (i true) ∧ ¬ AlgX true := by
  simp

theorem left_inverse_transfers_property
    {X Y : Type}
    (AlgX : X → Prop) (AlgY : Y → Prop)
    (i : X → Y) (r : Y → X)
    (hretract : Function.LeftInverse r i)
    (hpreserve : ∀ y, AlgY y → AlgX (r y)) :
    ∀ x, AlgY (i x) → AlgX x := by
  intro x hx
  exact retract_transfers_property AlgX AlgY i r x (hretract x) hpreserve hx

#print axioms retract_transfers_property
#print axioms retract_without_property_preservation_counterexample
#print axioms left_inverse_transfers_property

end B4Auto18Run8.Hodge

namespace B4Auto18Run8.NavierStokes

theorem critical_bubble_L3_cost_scale_invariant
    (r : ℝ) (hr : r ≠ 0) :
    (1 / r)^3 * r^3 = 1 := by
  field_simp [hr]

theorem arbitrarily_small_critical_scale_has_large_amplitude
    (M : ℝ) (hM : 0 ≤ M) :
    let r : ℝ := 1 / (M + 1)
    0 < r ∧ M < 1 / r := by
  dsimp
  have hden : 0 < M + 1 := by linarith
  constructor
  · positivity
  · have hne : M + 1 ≠ 0 := ne_of_gt hden
    field_simp [hne]
    linarith

theorem strong_L3_budget_bounds_critical_bubble_count
    (N E : ℝ) (hbudget : N * 1 ≤ E) :
    N ≤ E := by
  nlinarith

#print axioms critical_bubble_L3_cost_scale_invariant
#print axioms arbitrarily_small_critical_scale_has_large_amplitude
#print axioms strong_L3_budget_bounds_critical_bubble_count

end B4Auto18Run8.NavierStokes

namespace B4Auto18Run8.YangMills

theorem physical_gap_from_ratio_error
    (a M eps g : ℝ)
    (ha : 0 < a) (hmargin : eps < M)
    (herr : |g / a - M| ≤ eps) :
    0 < g / a ∧ M - eps ≤ g / a := by
  have hlow := (abs_le.mp herr).1
  constructor <;> linarith

theorem boundary_scaled_error_can_erase_gap
    (a : ℝ) (ha : 0 < a) :
    |(0 : ℝ) - a * 1| = a ∧ (0 : ℝ) / a = 0 := by
  constructor
  · simp [abs_of_pos ha]
  · simp

theorem strict_scaled_error_margin_gives_positive_physical_gap
    (a M eta g : ℝ)
    (ha : 0 < a) (hM : 0 < M) (heta : 0 ≤ eta) (hstrict : eta < M)
    (herr : |g - a * M| ≤ a * eta) :
    0 < g / a ∧ M - eta ≤ g / a := by
  have hlow := (abs_le.mp herr).1
  have hga : a * (M - eta) ≤ g := by
    nlinarith
  constructor
  · have hpos : 0 < a * (M - eta) := by
      exact mul_pos ha (sub_pos.mpr hstrict)
    have hg : 0 < g := lt_of_lt_of_le hpos hga
    exact div_pos hg ha
  · exact (le_div_iff₀ ha).2 hga

#print axioms physical_gap_from_ratio_error
#print axioms boundary_scaled_error_can_erase_gap
#print axioms strict_scaled_error_margin_gives_positive_physical_gap

end B4Auto18Run8.YangMills
