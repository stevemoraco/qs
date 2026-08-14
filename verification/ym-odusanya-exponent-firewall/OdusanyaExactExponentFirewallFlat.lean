import Mathlib

namespace Millennium.YangMills

theorem faster_exponential_below_slower
    {m q x : ℝ} (hqm : q ≤ m) (hx : 0 ≤ x) :
    Real.exp (-m * x) ≤ Real.exp (-q * x) := by
  apply Real.exp_le_exp.mpr
  nlinarith

theorem two_sided_exponential_bounds_do_not_identify_rate :
    ∃ (G : ℝ → ℝ) (m q : ℝ),
      0 < q ∧ q < m ∧
      ∀ x, 0 ≤ x →
        Real.exp (-m * x) ≤ G x ∧ G x ≤ Real.exp (-q * x) := by
  refine ⟨(fun x => Real.exp (-2 * x)), 2, 1, by norm_num, by norm_num, ?_⟩
  intro x hx
  constructor
  · rfl
  · exact faster_exponential_below_slower (m := (2 : ℝ)) (q := (1 : ℝ))
      (x := x) (by norm_num) hx

#print axioms faster_exponential_below_slower
#print axioms two_sided_exponential_bounds_do_not_identify_rate

end Millennium.YangMills
