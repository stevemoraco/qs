import Mathlib

/-!
# Exponential-rate identification firewall

This file isolates a load-bearing logical step in a claimed Yang--Mills
polymer-to-transfer-gap comparison.

If a positive correlation function has a lower exponential bound with rate
`m` and an upper exponential bound with a possibly smaller rate `r`, the two
bounds do not identify the rates.  Already with unit prefactors and the exact
correlator `G(t) = exp (-m*t)`, every pair `0 < r < m` satisfies

    exp (-m*t) <= G(t) <= exp (-r*t)    for t >= 0,

while `m != r`.

Thus a polymer decay upper bound and a transfer-matrix lower bound can at most
order the two exponents without an additional sharpness theorem.  This finite
firewall does not formalize Yang--Mills fields, transfer matrices, polymer
expansions, continuum limits, or Osterwalder--Schrader reconstruction.
-/

namespace Millennium.YangMills

/-- If `r <= m`, then on nonnegative times the faster rate `m` gives the
smaller exponential. -/
theorem exponential_rate_order_gives_bound
    (r m t : ℝ) (hrm : r ≤ m) (ht : 0 ≤ t) :
    Real.exp (-m * t) ≤ Real.exp (-r * t) := by
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- With unit prefactors at one positive time, the exponential inequality
forces only the ordering `r <= m`. -/
theorem unit_prefactor_exponential_bound_forces_rate_order
    (r m : ℝ)
    (h : Real.exp (-m) ≤ Real.exp (-r)) :
    r ≤ m := by
  have h' : -m ≤ -r := Real.exp_le_exp.mp h
  linarith

/-- Exact countermodel to identifying two unequal exponents from a lower
transfer-style exponential bound and an upper polymer-style exponential
bound. -/
theorem two_sided_exponential_bounds_do_not_identify_rates :
    ∃ (r m : ℝ) (G : ℝ → ℝ),
      0 < r ∧ r < m ∧
      (∀ t : ℝ, 0 ≤ t → Real.exp (-m * t) ≤ G t) ∧
      (∀ t : ℝ, 0 ≤ t → G t ≤ Real.exp (-r * t)) := by
  refine ⟨1, 2, (fun t : ℝ => Real.exp (-2 * t)), by norm_num, by norm_num, ?_, ?_⟩
  · intro t ht
    exact le_rfl
  · intro t ht
    exact exponential_rate_order_gives_bound 1 2 t (by norm_num) ht

/-- Stronger parametric form: every strictly separated pair `r < m` admits
the source-shaped two-sided bounds with `G(t)=exp(-m*t)`. In particular this
applies to every physical pair `0 < r < m`. -/
theorem arbitrary_strict_rate_separation_is_compatible
    (r m : ℝ) (hrm : r < m) :
    ∃ G : ℝ → ℝ,
      (∀ t : ℝ, 0 ≤ t → Real.exp (-m * t) ≤ G t) ∧
      (∀ t : ℝ, 0 ≤ t → G t ≤ Real.exp (-r * t)) := by
  refine ⟨(fun t : ℝ => Real.exp (-m * t)), ?_, ?_⟩
  · intro t ht
    exact le_rfl
  · intro t ht
    exact exponential_rate_order_gives_bound r m t (le_of_lt hrm) ht

#print axioms exponential_rate_order_gives_bound
#print axioms unit_prefactor_exponential_bound_forces_rate_order
#print axioms two_sided_exponential_bounds_do_not_identify_rates
#print axioms arbitrary_strict_rate_separation_is_compatible

end Millennium.YangMills
