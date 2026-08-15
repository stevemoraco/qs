import Mathlib

/-!
# Exact Fatou residual series from a backward quadratic RG budget

Flattened verifier source. This file proves only finite/functional-analytic
statements. It does not prove any Yang--Mills RG estimate, continuum limit,
OS theorem, mass gap, or Clay statement.
-/

namespace Millennium.YangMills

theorem sum_range_backward_differences
    (u : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (u n - u (n + 1))) = u 0 - u N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

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

noncomputable def dyadicFatouLambda
    (psi : ℝ → ℝ) (ell u : ℝ) : ℝ :=
  Real.exp (-(Real.log 2) * psi u) / ell

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

/-- Recursive backward orbit of a local inverse RG map. -/
def inverseOrbit (G : ℝ → ℝ) (u : ℝ) : ℕ → ℝ
  | 0 => u
  | n + 1 => G (inverseOrbit G u n)

@[simp] theorem inverseOrbit_zero (G : ℝ → ℝ) (u : ℝ) :
    inverseOrbit G u 0 = u := rfl

@[simp] theorem inverseOrbit_succ (G : ℝ → ℝ) (u : ℝ) (n : ℕ) :
    inverseOrbit G u (n + 1) = G (inverseOrbit G u n) := rfl

theorem inverseOrbit_forward_shift
    (G F : ℝ → ℝ) (u : ℝ)
    (hGF : G (F u) = u) :
    ∀ n, inverseOrbit G (F u) (n + 1) = inverseOrbit G u n := by
  intro n
  induction n with
  | zero =>
      simpa using hGF
  | succ n ih =>
      rw [inverseOrbit_succ]
      rw [inverseOrbit_succ]
      exact congrArg G ih

theorem inverseOrbit_residual_abs_summable
    (G rho : ℝ → ℝ) (u : ℝ)
    {beta K : ℝ}
    (hbeta : 0 < beta)
    (hK : 0 ≤ K)
    (hnonneg : ∀ n, 0 ≤ inverseOrbit G u n)
    (hgrowth : ∀ n,
      beta * (inverseOrbit G u (n + 1))^2 ≤
        inverseOrbit G u n - inverseOrbit G u (n + 1))
    (hlocal : ∀ n,
      |rho (inverseOrbit G u (n + 1))| ≤
        K * (inverseOrbit G u (n + 1))^2) :
    Summable (fun n => |rho (inverseOrbit G u (n + 1))|) := by
  apply summable_of_sum_range_le
  · intro n
    exact abs_nonneg _
  · intro N
    exact backward_quadratic_error_budget_uniform
      (inverseOrbit G u)
      (fun n => rho (inverseOrbit G u (n + 1)))
      N hbeta hK (hnonneg N)
      (fun n _ => hgrowth n)
      (fun n _ => hlocal n)

theorem inverseOrbit_residual_summable
    (G rho : ℝ → ℝ) (u : ℝ)
    {beta K : ℝ}
    (hbeta : 0 < beta)
    (hK : 0 ≤ K)
    (hnonneg : ∀ n, 0 ≤ inverseOrbit G u n)
    (hgrowth : ∀ n,
      beta * (inverseOrbit G u (n + 1))^2 ≤
        inverseOrbit G u n - inverseOrbit G u (n + 1))
    (hlocal : ∀ n,
      |rho (inverseOrbit G u (n + 1))| ≤
        K * (inverseOrbit G u (n + 1))^2) :
    Summable (fun n => rho (inverseOrbit G u n)) := by
  have habs := inverseOrbit_residual_abs_summable
    G rho u hbeta hK hnonneg hgrowth hlocal
  have htail : Summable (fun n => rho (inverseOrbit G u (n + 1))) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using habs
  exact htail.comp_nat_add

noncomputable def fatouCorrection
    (rho G : ℝ → ℝ) (u : ℝ) : ℝ :=
  - ∑' n : ℕ, rho (inverseOrbit G u (n + 1))

theorem fatouCorrection_abs_le
    (G rho : ℝ → ℝ) (u : ℝ)
    {beta K : ℝ}
    (hbeta : 0 < beta)
    (hK : 0 ≤ K)
    (hnonneg : ∀ n, 0 ≤ inverseOrbit G u n)
    (hgrowth : ∀ n,
      beta * (inverseOrbit G u (n + 1))^2 ≤
        inverseOrbit G u n - inverseOrbit G u (n + 1))
    (hlocal : ∀ n,
      |rho (inverseOrbit G u (n + 1))| ≤
        K * (inverseOrbit G u (n + 1))^2) :
    |fatouCorrection rho G u| ≤ (K / beta) * u := by
  have habs := inverseOrbit_residual_abs_summable
    G rho u hbeta hK hnonneg hgrowth hlocal
  have htsumAbs :
      (∑' n : ℕ, |rho (inverseOrbit G u (n + 1))|) ≤
        (K / beta) * u := by
    apply Real.tsum_le_of_sum_range_le
    · intro n
      exact abs_nonneg _
    · intro N
      exact backward_quadratic_error_budget_uniform
        (inverseOrbit G u)
        (fun n => rho (inverseOrbit G u (n + 1)))
        N hbeta hK (hnonneg N)
        (fun n _ => hgrowth n)
        (fun n _ => hlocal n)
  have hnorm :
      Summable (fun n : ℕ => ‖rho (inverseOrbit G u (n + 1))‖) := by
    simpa only [Real.norm_eq_abs] using habs
  have hnormTsum :
      ‖∑' n : ℕ, rho (inverseOrbit G u (n + 1))‖ ≤
        ∑' n : ℕ, ‖rho (inverseOrbit G u (n + 1))‖ :=
    norm_tsum_le_tsum_norm hnorm
  calc
    |fatouCorrection rho G u| =
        |∑' n : ℕ, rho (inverseOrbit G u (n + 1))| := by
          simp [fatouCorrection]
    _ = ‖∑' n : ℕ, rho (inverseOrbit G u (n + 1))‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∑' n : ℕ, ‖rho (inverseOrbit G u (n + 1))‖ := hnormTsum
    _ = ∑' n : ℕ, |rho (inverseOrbit G u (n + 1))| := by
          simp only [Real.norm_eq_abs]
    _ ≤ (K / beta) * u := htsumAbs

theorem fatouCorrection_shift
    (rho G F : ℝ → ℝ) (u : ℝ)
    (hGF : G (F u) = u)
    (hsum : Summable (fun n => rho (inverseOrbit G u n))) :
    fatouCorrection rho G (F u) =
      -rho u + fatouCorrection rho G u := by
  have htsum :
      (∑' n : ℕ, rho (inverseOrbit G (F u) (n + 1))) =
        ∑' n : ℕ, rho (inverseOrbit G u n) := by
    apply tsum_congr
    intro n
    rw [inverseOrbit_forward_shift G F u hGF n]
  have hsplit :
      rho u + (∑' n : ℕ, rho (inverseOrbit G u (n + 1))) =
        ∑' n : ℕ, rho (inverseOrbit G u n) := by
    simpa using hsum.sum_add_tsum_nat_add 1
  rw [fatouCorrection, fatouCorrection, htsum, ← hsplit]
  ring

noncomputable def exactFatouPsi
    (phi rho G : ℝ → ℝ) (u : ℝ) : ℝ :=
  phi u + fatouCorrection rho G u

theorem exactFatouPsi_abel
    (phi rho G F : ℝ → ℝ) (u : ℝ)
    (hGF : G (F u) = u)
    (hsum : Summable (fun n => rho (inverseOrbit G u n)))
    (hresid : rho u = phi (F u) - phi u + 1) :
    exactFatouPsi phi rho G (F u) =
      exactFatouPsi phi rho G u - 1 := by
  rw [exactFatouPsi, exactFatouPsi,
    fatouCorrection_shift rho G F u hGF hsum, hresid]
  ring

theorem exactFatouPsi_abel_of_quadratic_budget
    (phi rho G F : ℝ → ℝ) (u : ℝ)
    {beta K : ℝ}
    (hbeta : 0 < beta)
    (hK : 0 ≤ K)
    (hGF : G (F u) = u)
    (hnonneg : ∀ n, 0 ≤ inverseOrbit G u n)
    (hgrowth : ∀ n,
      beta * (inverseOrbit G u (n + 1))^2 ≤
        inverseOrbit G u n - inverseOrbit G u (n + 1))
    (hlocal : ∀ n,
      |rho (inverseOrbit G u (n + 1))| ≤
        K * (inverseOrbit G u (n + 1))^2)
    (hresid : rho u = phi (F u) - phi u + 1) :
    exactFatouPsi phi rho G (F u) =
      exactFatouPsi phi rho G u - 1 := by
  exact exactFatouPsi_abel phi rho G F u hGF
    (inverseOrbit_residual_summable
      G rho u hbeta hK hnonneg hgrowth hlocal)
    hresid

theorem exactFatouLambda_invariant_of_quadratic_budget
    (phi rho G F : ℝ → ℝ) (ell u : ℝ)
    {beta K : ℝ}
    (hell : ell ≠ 0)
    (hbeta : 0 < beta)
    (hK : 0 ≤ K)
    (hGF : G (F u) = u)
    (hnonneg : ∀ n, 0 ≤ inverseOrbit G u n)
    (hgrowth : ∀ n,
      beta * (inverseOrbit G u (n + 1))^2 ≤
        inverseOrbit G u n - inverseOrbit G u (n + 1))
    (hlocal : ∀ n,
      |rho (inverseOrbit G u (n + 1))| ≤
        K * (inverseOrbit G u (n + 1))^2)
    (hresid : rho u = phi (F u) - phi u + 1) :
    dyadicFatouLambda (exactFatouPsi phi rho G) (2 * ell) (F u) =
      dyadicFatouLambda (exactFatouPsi phi rho G) ell u := by
  apply dyadicFatouLambda_invariant
  · exact hell
  · exact exactFatouPsi_abel_of_quadratic_budget
      phi rho G F u hbeta hK hGF hnonneg hgrowth hlocal hresid

#print axioms inverseOrbit_forward_shift
#print axioms inverseOrbit_residual_abs_summable
#print axioms inverseOrbit_residual_summable
#print axioms fatouCorrection_abs_le
#print axioms fatouCorrection_shift
#print axioms exactFatouPsi_abel
#print axioms exactFatouPsi_abel_of_quadratic_budget
#print axioms exactFatouLambda_invariant_of_quadratic_budget

end Millennium.YangMills
