import Mathlib

/-!
# Navier--Stokes compact-gap exponent firewall

This file formalizes only the scalar compact counterexample `d(x)=x^4` to the
implication

  compact domain + continuous nonnegative defect + exact zero set
    -> distance^2 <= C * defect.

It does not formalize active-frame measures, Littlewood--Paley packets, passive
strain, or Navier--Stokes.
-/

namespace MillenniumBraid
namespace B2Round42NS

/-- The polynomial defect used in the compact counterexample. -/
def quarticDefect (x : ℝ) : ℝ := x ^ 4

/-- The unit interval supplying the compact ambient space. -/
def compactDomain : Set ℝ := Set.Icc 0 1

/-- The ambient domain is compact. -/
theorem compactDomain_isCompact : IsCompact compactDomain := by
  exact isCompact_Icc

/-- The defect is continuous. -/
theorem quarticDefect_continuous : Continuous quarticDefect := by
  unfold quarticDefect
  fun_prop

/-- The defect is nonnegative. -/
theorem quarticDefect_nonnegative (x : ℝ) :
    0 ≤ quarticDefect x := by
  unfold quarticDefect
  positivity

/-- The defect has exactly the singleton zero set. -/
theorem quarticDefect_zero_iff (x : ℝ) :
    quarticDefect x = 0 ↔ x = 0 := by
  simp [quarticDefect]

/-- Compactness does give a fixed-distance positive gap: if `x ≥ ε ≥ 0`, then
`d(x) ≥ ε^4`. -/
theorem quartic_fixed_distance_gap
    {ε x : ℝ} (hε : 0 ≤ ε) (hx : ε ≤ x) :
    ε ^ 4 ≤ quarticDefect x := by
  have hx0 : 0 ≤ x := le_trans hε hx
  have hsq : ε ^ 2 ≤ x ^ 2 := by
    nlinarith [sq_nonneg (x - ε)]
  have hdiff : 0 ≤ x ^ 2 - ε ^ 2 := sub_nonneg.mpr hsq
  have hsum : 0 ≤ x ^ 2 + ε ^ 2 := by positivity
  have hprod : 0 ≤ (x ^ 2 - ε ^ 2) * (x ^ 2 + ε ^ 2) :=
    mul_nonneg hdiff hsum
  unfold quarticDefect
  nlinarith

/-- The exact order-four Łojasiewicz-style inequality is an equality. -/
theorem quartic_order_four_exact (x : ℝ) :
    x ^ 4 = quarticDefect x := by
  rfl

/-- For every proposed nonnegative quadratic-gap constant, there is an explicit
point of the compact interval where `C*x^4 < x^2`. -/
theorem no_uniform_quadratic_gap
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ x : ℝ,
      x ∈ compactDomain ∧
      C * quarticDefect x < x ^ 2 := by
  let x : ℝ := 1 / (C + 1)
  have hden : 0 < C + 1 := by linarith
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hxone : x ≤ 1 := by
    dsimp [x]
    rw [div_le_iff₀ hden]
    linarith
  have hlt : C < (C + 1) ^ 2 := by
    nlinarith [sq_nonneg C]
  have hfrac : C / (C + 1) ^ 2 < 1 := by
    exact (div_lt_one (sq_pos_of_pos hden)).2 hlt
  have hcx2 : C * x ^ 2 < 1 := by
    calc
      C * x ^ 2 = C / (C + 1) ^ 2 := by
        dsimp [x]
        field_simp [ne_of_gt hden]
        <;> ring
      _ < 1 := hfrac
  have hx2pos : 0 < x ^ 2 := sq_pos_of_pos hxpos
  refine ⟨x, ⟨le_of_lt hxpos, hxone⟩, ?_⟩
  unfold quarticDefect
  calc
    C * x ^ 4 = (C * x ^ 2) * x ^ 2 := by ring
    _ < 1 * x ^ 2 := mul_lt_mul_of_pos_right hcx2 hx2pos
    _ = x ^ 2 := one_mul _

/-- Consequently no nonnegative constant controls squared distance by the
quartic defect on the full compact interval. -/
theorem no_global_quadratic_error_bound :
    ¬ ∃ C : ℝ,
      0 ≤ C ∧
      ∀ x ∈ compactDomain, x ^ 2 ≤ C * quarticDefect x := by
  rintro ⟨C, hC, hall⟩
  obtain ⟨x, hx, hstrict⟩ := no_uniform_quadratic_gap C hC
  exact (not_lt_of_ge (hall x hx)) hstrict

#print axioms compactDomain_isCompact
#print axioms quarticDefect_continuous
#print axioms quarticDefect_nonnegative
#print axioms quarticDefect_zero_iff
#print axioms quartic_fixed_distance_gap
#print axioms quartic_order_four_exact
#print axioms no_uniform_quadratic_gap
#print axioms no_global_quadratic_error_bound

end B2Round42NS
end MillenniumBraid
