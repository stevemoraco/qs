import Mathlib

namespace B4Auto16Run10.RH

theorem nearby_sample_transfer
    {x y ω ε : ℝ}
    (hmod : |x - y| ≤ ω)
    (hsample : |y| ≤ ε) :
    |x| ≤ ω + ε := by
  have hm := abs_le.mp hmod
  have hs := abs_le.mp hsample
  apply abs_le.mpr
  constructor <;> linarith

theorem sample_only_not_uniform_counterexample :
    ∃ x y : ℝ,
      |y| ≤ 0 ∧
      1 < |x| := by
  refine ⟨2, 0, ?_, ?_⟩ <;> norm_num

theorem mesh_margin_closes_strict_target
    {x y ω ε τ : ℝ}
    (hmod : |x - y| ≤ ω)
    (hsample : |y| ≤ ε)
    (hmargin : ω + ε < τ) :
    |x| < τ := by
  exact lt_of_le_of_lt (nearby_sample_transfer hmod hsample) hmargin

#print axioms nearby_sample_transfer
#print axioms sample_only_not_uniform_counterexample
#print axioms mesh_margin_closes_strict_target
end B4Auto16Run10.RH

namespace B4Auto16Run10.PNP

def Solves (d x : Bool) : Prop := d = x

theorem every_fixed_decoder_has_failure :
    ∀ d : Bool, ∃ x : Bool, ¬ Solves d x := by
  intro d
  cases d with
  | false =>
      refine ⟨true, ?_⟩
      simp [Solves]
  | true =>
      refine ⟨false, ?_⟩
      simp [Solves]

theorem input_dependent_selector_solves_all :
    ∃ select : Bool → Bool,
      ∀ x : Bool, Solves (select x) x := by
  refine ⟨fun x => x, ?_⟩
  intro x
  rfl

theorem fixed_decoder_separation_rule
    {C X : Type*}
    (solves : C → X → Prop)
    (hhard : ∀ c : C, ∃ x : X, ¬ solves c x) :
    ¬ ∃ c : C, ∀ x : X, solves c x := by
  rintro ⟨c, hc⟩
  rcases hhard c with ⟨x, hx⟩
  exact hx (hc x)

#print axioms every_fixed_decoder_has_failure
#print axioms input_dependent_selector_solves_all
#print axioms fixed_decoder_separation_rule
end B4Auto16Run10.PNP

namespace B4Auto16Run10.BSD

theorem omitted_local_term_lower_bound
    {global kept omitted : ℕ}
    (hglobal : global = kept + omitted) :
    kept ≤ global := by
  omega

theorem positive_omitted_term_forces_mismatch
    {global kept omitted : ℕ}
    (hglobal : global = kept + omitted)
    (homit : 0 < omitted) :
    kept < global := by
  omega

theorem truncated_equality_forces_omitted_zero
    {global kept omitted : ℕ}
    (hglobal : global = kept + omitted)
    (htruncated : global = kept) :
    omitted = 0 := by
  omega

theorem one_unit_omission_counterexample :
    ∃ global kept omitted : ℕ,
      global = kept + omitted ∧
      0 < omitted ∧
      global ≠ kept := by
  refine ⟨3, 2, 1, by omega, by omega, by omega⟩

#print axioms omitted_local_term_lower_bound
#print axioms positive_omitted_term_forces_mismatch
#print axioms truncated_equality_forces_omitted_zero
#print axioms one_unit_omission_counterexample
end B4Auto16Run10.BSD

namespace B4Auto16Run10.Hodge

theorem retract_transfers_algebraicity
    {X Y : Type*}
    (HodgeX AlgebraicX : X → Prop)
    (HodgeY AlgebraicY : Y → Prop)
    (up : X → Y)
    (down : Y → X)
    (hretract : ∀ x : X, down (up x) = x)
    (hodge_up : ∀ x : X, HodgeX x → HodgeY (up x))
    (target_hodge_algebraic : ∀ y : Y, HodgeY y → AlgebraicY y)
    (algebraic_down : ∀ y : Y, AlgebraicY y → AlgebraicX (down y)) :
    ∀ x : X, HodgeX x → AlgebraicX x := by
  intro x hx
  have hyH : HodgeY (up x) := hodge_up x hx
  have hyA : AlgebraicY (up x) := target_hodge_algebraic (up x) hyH
  have hxA : AlgebraicX (down (up x)) := algebraic_down (up x) hyA
  simpa [hretract x] using hxA

theorem no_retract_transfer_counterexample :
    ∃ (HodgeX AlgebraicX : Bool → Prop)
      (HodgeY AlgebraicY : Unit → Prop)
      (up : Bool → Unit) (down : Unit → Bool),
      (∀ x, HodgeX x → HodgeY (up x)) ∧
      (∀ y, HodgeY y → AlgebraicY y) ∧
      (∀ y, AlgebraicY y → AlgebraicX (down y)) ∧
      ¬ (∀ x, HodgeX x → AlgebraicX x) := by
  refine ⟨fun _ => True, fun x => x = false,
    fun _ => True, fun _ => True,
    fun _ => (), fun _ => false, ?_, ?_, ?_, ?_⟩
  · intro x hx
    trivial
  · intro y hy
    trivial
  · intro y hy
    rfl
  · intro hall
    have h := hall true trivial
    simp at h

#print axioms retract_transfers_algebraicity
#print axioms no_retract_transfer_counterexample
end B4Auto16Run10.Hodge

namespace B4Auto16Run10.NS

theorem uniform_positive_price_bounds_count
    {N : ℕ} {c E : ℝ}
    (hc : 0 < c)
    (hbudget : (N : ℝ) * c ≤ E) :
    (N : ℝ) ≤ E / c := by
  exact (le_div_iff₀ hc).2 hbudget

theorem arbitrarily_many_positive_events_unit_budget
    (N : ℕ)
    (hN : 0 < N) :
    ∃ c : ℝ,
      0 < c ∧
      (N : ℝ) * c = 1 := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNr
  refine ⟨1 / (N : ℝ), ?_, ?_⟩
  · positivity
  · field_simp [hN0]

theorem positivity_without_uniform_floor_has_no_count_ceiling
    (B : ℕ) :
    ∃ N : ℕ, ∃ c : ℝ,
      B < N ∧
      0 < c ∧
      (N : ℝ) * c = 1 := by
  let N := B + 1
  have hBN : B < N := by
    dsimp [N]
    omega
  have hN : 0 < N := by
    omega
  rcases arbitrarily_many_positive_events_unit_budget N hN with ⟨c, hc, hcost⟩
  exact ⟨N, c, hBN, hc, hcost⟩

#print axioms uniform_positive_price_bounds_count
#print axioms arbitrarily_many_positive_events_unit_budget
#print axioms positivity_without_uniform_floor_has_no_count_ceiling
end B4Auto16Run10.NS

namespace B4Auto16Run10.YM

theorem scale_aware_error_gives_physical_bound
    {a η M : ℝ}
    (ha : 0 < a)
    (hscale : η ≤ M * a) :
    η / a ≤ M := by
  exact (div_le_iff₀ ha).2 hscale

theorem small_absolute_error_large_physical_error_counterexample :
    ∃ a η : ℝ,
      0 < a ∧
      0 < η ∧
      η < 1 ∧
      10 < η / a := by
  refine ⟨1 / 100, 1 / 5, ?_, ?_, ?_, ?_⟩ <;> norm_num

theorem strict_scale_aware_error_gives_physical_bound
    {a η M : ℝ}
    (ha : 0 < a)
    (hscale : η < M * a) :
    η / a < M := by
  exact (div_lt_iff₀ ha).2 hscale

#print axioms scale_aware_error_gives_physical_bound
#print axioms small_absolute_error_large_physical_error_counterexample
#print axioms strict_scale_aware_error_gives_physical_bound
end B4Auto16Run10.YM
