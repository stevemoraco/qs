import Mathlib

/-!
# Exact Fatou-coordinate Lambda bridge for a two-loop RG map

Finite/load-bearing statements behind an exact thermodynamic
dimensional-transmutation scale.  This source does not prove any Yang--Mills
RG estimate, mass gap, continuum limit, or Clay statement.
-/

namespace Millennium.YangMills

/-- Backward differences telescope over a finite ultraviolet trajectory. -/
theorem sum_range_backward_differences
    (u : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (u n - u (n + 1))) = u 0 - u N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- If the inverse RG trajectory pays at least `beta * u^2` per backward step,
then any local error bounded by `K * u^2` has a finite endpoint budget. -/
theorem backward_quadratic_error_budget
    (u err : ℕ → ℝ) (N : ℕ)
    {beta K : ℝ}
    (hbeta : 0 < beta)
    (hK : 0 ≤ K)
    (hgrowth : ∀ n < N,
      beta * (u (n + 1))^2 ≤ u n - u (n + 1))
    (hlocal : ∀ n < N,
      |err n| ≤ K * (u (n + 1))^2) :
    (∑ n ∈ Finset.range N, |err n|) ≤
      (K / beta) * (u 0 - u N) := by
  have hcoef : 0 ≤ K / beta :=
    div_nonneg hK (le_of_lt hbeta)
  have hpoint : ∀ n ∈ Finset.range N,
      |err n| ≤ (K / beta) * (u n - u (n + 1)) := by
    intro n hn
    have hnlt : n < N := Finset.mem_range.mp hn
    calc
      |err n| ≤ K * (u (n + 1))^2 := hlocal n hnlt
      _ = (K / beta) * (beta * (u (n + 1))^2) := by
        field_simp [ne_of_gt hbeta]
      _ ≤ (K / beta) * (u n - u (n + 1)) :=
        mul_le_mul_of_nonneg_left (hgrowth n hnlt) hcoef
  calc
    (∑ n ∈ Finset.range N, |err n|) ≤
        ∑ n ∈ Finset.range N, (K / beta) * (u n - u (n + 1)) :=
      Finset.sum_le_sum hpoint
    _ = (K / beta) * (u 0 - u N) := by
      rw [← Finset.mul_sum]
      rw [sum_range_backward_differences]

/-- If the backward trajectory remains nonnegative, every finite partial error
sum is bounded by one regulator-independent multiple of its starting coupling.
This is the uniform Cauchy budget used for the Fatou correction series. -/
theorem backward_quadratic_error_budget_uniform
    (u err : ℕ → ℝ) (N : ℕ)
    {beta K : ℝ}
    (hbeta : 0 < beta)
    (hK : 0 ≤ K)
    (huN : 0 ≤ u N)
    (hgrowth : ∀ n < N,
      beta * (u (n + 1))^2 ≤ u n - u (n + 1))
    (hlocal : ∀ n < N,
      |err n| ≤ K * (u (n + 1))^2) :
    (∑ n ∈ Finset.range N, |err n|) ≤
      (K / beta) * u 0 := by
  have hcoef : 0 ≤ K / beta :=
    div_nonneg hK (le_of_lt hbeta)
  have hendpoint : u 0 - u N ≤ u 0 := by
    linarith
  exact le_trans
    (backward_quadratic_error_budget
      u err N hbeta hK hgrowth hlocal)
    (mul_le_mul_of_nonneg_left hendpoint hcoef)

/-- Exact scale associated with a real Abel/Fatou coordinate for a dyadic RG
step. -/
noncomputable def dyadicFatouLambda
    (psi : ℝ → ℝ) (ell u : ℝ) : ℝ :=
  Real.exp (-(Real.log 2) * psi u) / ell

/-- The Abel equation `psi(F u) = psi(u) - 1` makes the scale exactly invariant
under the factor-two RG step `(ell,u) ↦ (2 ell, F u)`. -/
theorem dyadicFatouLambda_invariant
    (psi F : ℝ → ℝ) (ell u : ℝ)
    (hell : ell ≠ 0)
    (hAbel : psi (F u) = psi u - 1) :
    dyadicFatouLambda psi (2 * ell) (F u) =
      dyadicFatouLambda psi ell u := by
  rw [dyadicFatouLambda, dyadicFatouLambda, hAbel]
  have htwo : Real.exp (Real.log (2 : ℝ)) = 2 := by
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [show
    -(Real.log (2 : ℝ)) * (psi u - 1) =
      -(Real.log (2 : ℝ)) * psi u + Real.log (2 : ℝ) by ring]
  rw [Real.exp_add, htwo]
  field_simp [hell]

#print axioms sum_range_backward_differences
#print axioms backward_quadratic_error_budget
#print axioms backward_quadratic_error_budget_uniform
#print axioms dyadicFatouLambda_invariant

end Millennium.YangMills
