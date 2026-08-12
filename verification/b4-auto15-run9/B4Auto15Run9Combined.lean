import Mathlib

namespace B4Auto15Run9.RH

theorem two_point_bad_windows_cost
    {x y τ E : ℝ}
    (hx : τ ≤ x)
    (hy : τ ≤ y)
    (hbudget : x + y ≤ E) :
    2 * τ ≤ E := by
  linarith

theorem average_control_not_uniform_counterexample :
    ∃ x y : ℝ,
      0 ≤ x ∧ 0 ≤ y ∧
      (x + y) / 2 ≤ 1 ∧
      1 < y := by
  refine ⟨0, 2, by norm_num, by norm_num, ?_, by norm_num⟩
  norm_num

theorem one_bad_window_cost
    {x y τ E : ℝ}
    (hy0 : 0 ≤ y)
    (hx : τ ≤ x)
    (hbudget : x + y ≤ E) :
    τ ≤ E := by
  linarith

#print axioms two_point_bad_windows_cost
#print axioms average_control_not_uniform_counterexample
#print axioms one_bad_window_cost
end B4Auto15Run9.RH

namespace B4Auto15Run9.PNP

theorem conditioned_error_budget
    {goodMass badMass goodErr badErr ε δ : ℝ}
    (hgoodMass0 : 0 ≤ goodMass)
    (hgoodMass1 : goodMass ≤ 1)
    (hbadMass : badMass ≤ ε)
    (hgoodErr : goodErr ≤ δ * goodMass)
    (hbadErr : badErr ≤ badMass)
    (hδ0 : 0 ≤ δ) :
    goodErr + badErr ≤ δ + ε := by
  have hscale : δ * goodMass ≤ δ := by
    nlinarith
  linarith

theorem conditioning_does_not_preserve_universal_counterexample :
    ∃ P : Bool → Prop,
      P false ∧ ¬ (∀ b, P b) := by
  refine ⟨fun b => b = false, rfl, ?_⟩
  intro h
  have ht := h true
  simp at ht

theorem two_sector_universal_closure
    {P : Bool → Prop}
    (hfalse : P false)
    (htrue : P true) :
    ∀ b, P b := by
  intro b
  cases b <;> assumption

#print axioms conditioned_error_budget
#print axioms conditioning_does_not_preserve_universal_counterexample
#print axioms two_sector_universal_closure
end B4Auto15Run9.PNP

namespace B4Auto15Run9.BSD

theorem two_local_defects_sum_bound
    {a b k : ℕ}
    (ha : a ≤ k)
    (hb : b ≤ k) :
    a + b ≤ 2 * k := by
  omega

theorem scalar_ceiling_not_local_sum_counterexample :
    ∃ a b k : ℕ,
      a ≤ k ∧ b ≤ k ∧ k < a + b := by
  refine ⟨2, 3, 3, by omega, by omega, by omega⟩

theorem zero_total_defect_forces_local_zero
    {a b : ℕ}
    (h : a + b = 0) :
    a = 0 ∧ b = 0 := by
  omega

#print axioms two_local_defects_sum_bound
#print axioms scalar_ceiling_not_local_sum_counterexample
#print axioms zero_total_defect_forces_local_zero
end B4Auto15Run9.BSD

namespace B4Auto15Run9.Hodge

theorem diagonal_injective_not_total_counterexample :
    ∃ f : Bool × Bool → Bool,
      (∀ x y : Bool, f (x, false) = f (y, false) → x = y) ∧
      ¬ Function.Injective f := by
  refine ⟨fun p => p.1, ?_, ?_⟩
  · intro x y h
    exact h
  · intro hinj
    have hpair : (false, false) = (false, true) := hinj rfl
    have hsnd := congrArg Prod.snd hpair
    simp at hsnd

theorem diagonal_injective_closes_when_cross_subsingleton
    {D C T : Type*}
    [Subsingleton C]
    (c0 : C)
    (f : D × C → T)
    (hdiag : Function.Injective (fun d => f (d, c0))) :
    Function.Injective f := by
  intro x y hxy
  rcases x with ⟨dx, cx⟩
  rcases y with ⟨dy, cy⟩
  have hcx : cx = c0 := Subsingleton.elim _ _
  have hcy : cy = c0 := Subsingleton.elim _ _
  subst cx
  subst cy
  have hd : dx = dy := hdiag hxy
  subst dy
  rfl

#print axioms diagonal_injective_not_total_counterexample
#print axioms diagonal_injective_closes_when_cross_subsingleton
end B4Auto15Run9.Hodge

namespace B4Auto15Run9.NS

theorem variable_persistence_charge_budget
    {ι : Type*}
    (s : Finset ι)
    (lower charge : ι → ℝ)
    {C E : ℝ}
    (hpoint : ∀ i ∈ s, lower i ≤ charge i)
    (hbudget : s.sum charge ≤ C * E) :
    s.sum lower ≤ C * E := by
  have hsum : s.sum lower ≤ s.sum charge :=
    Finset.sum_le_sum (fun i hi => hpoint i hi)
  exact hsum.trans hbudget

theorem uniform_episode_price_budget
    {ι : Type*}
    (s : Finset ι)
    (charge : ι → ℝ)
    {c C E : ℝ}
    (hpoint : ∀ i ∈ s, c ≤ charge i)
    (hbudget : s.sum charge ≤ C * E) :
    (s.card : ℝ) * c ≤ C * E := by
  have hsum : s.sum (fun _ => c) ≤ s.sum charge :=
    Finset.sum_le_sum (fun i hi => hpoint i hi)
  have hconst : s.sum (fun _ => c) = (s.card : ℝ) * c := by
    simp
  rw [hconst] at hsum
  exact hsum.trans hbudget

theorem zero_price_budget_does_not_kill_events :
    ∃ charges : Fin 2 → ℝ,
      (∀ i, charges i = 0) ∧
      (∑ i, charges i) = 0 := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro i
    rfl
  · simp

#print axioms variable_persistence_charge_budget
#print axioms uniform_episode_price_budget
#print axioms zero_price_budget_does_not_kill_events
end B4Auto15Run9.NS

namespace B4Auto15Run9.YM

theorem scaled_gap_survives_additive_error
    {a m ε observed trueGap : ℝ}
    (ha : 0 < a)
    (herr : |observed - trueGap| ≤ a * ε)
    (hobs : a * (m + ε) ≤ observed) :
    m ≤ trueGap / a := by
  have hdiff : observed - trueGap ≤ a * ε := (abs_le.mp herr).2
  have htrue : m * a ≤ trueGap := by
    nlinarith
  exact (le_div_iff₀ ha).2 htrue

theorem positive_lattice_gap_no_uniform_physical_floor
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ a g : ℝ,
      0 < a ∧ 0 < g ∧ g / a < ε := by
  refine ⟨1, ε / 2, by norm_num, by positivity, ?_⟩
  norm_num
  linarith

theorem strict_scaled_gap_survives_additive_error
    {a m ε observed trueGap : ℝ}
    (ha : 0 < a)
    (herr : |observed - trueGap| ≤ a * ε)
    (hobs : a * (m + ε) < observed) :
    m < trueGap / a := by
  have hdiff : observed - trueGap ≤ a * ε := (abs_le.mp herr).2
  have htrue : m * a < trueGap := by
    nlinarith
  exact (lt_div_iff₀ ha).2 htrue

#print axioms scaled_gap_survives_additive_error
#print axioms positive_lattice_gap_no_uniform_physical_floor
#print axioms strict_scaled_gap_survives_additive_error
end B4Auto15Run9.YM
