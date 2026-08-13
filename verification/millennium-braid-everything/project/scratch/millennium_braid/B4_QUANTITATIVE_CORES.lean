import Mathlib

/-!
Lean-ready finite cores for the Millennium B4 bank.

These are deliberately problem-independent.  They formalize two load-bearing
quantitative facts used by the current research braid:

1. the quartic-defect counterexample showing that compactness + continuity +
   exact zero-set identification do not imply a quadratic metric error bound;
2. the algebraic core of the corrected spectral defect-capacity inequality.

No Millennium conjecture is asserted here.
-/

namespace MillenniumB4

section QuarticDefect

/-- The model defect `x ↦ x^4` is continuous. -/
theorem quartic_defect_continuous : Continuous (fun x : ℝ => x ^ 4) := by
  fun_prop

/-- The model defect is nonnegative. -/
theorem quartic_defect_nonneg (x : ℝ) : 0 ≤ x ^ 4 := by
  positivity

/-- The model defect has exactly the zero set `{0}`. -/
theorem quartic_defect_zero_iff (x : ℝ) : x ^ 4 = 0 ↔ x = 0 := by
  simp

/--
For every proposed quadratic-error-bound constant `C`, there is an explicit
`x ∈ (0,1]` for which `C x^4 < x^2`.

This is the finite algebraic obstruction underlying the audit of any argument
that tries to deduce `dist^2 ≤ C * defect` from compactness, continuity and
zero-set identification alone.
-/
theorem quartic_not_quadratically_coercive (C : ℝ) :
    ∃ x : ℝ, 0 < x ∧ x ≤ 1 ∧ C * x ^ 4 < x ^ 2 := by
  let a : ℝ := |C| + 1
  have ha : 0 < a := by
    dsimp [a]
    linarith [abs_nonneg C]
  have ha1 : 1 ≤ a := by
    dsimp [a]
    linarith [abs_nonneg C]
  have hCa : C < a := by
    dsimp [a]
    linarith [le_abs_self C]
  have haa : a ≤ a ^ 2 := by
    nlinarith
  have hCa2 : C < a ^ 2 := lt_of_lt_of_le hCa haa
  let x : ℝ := 1 / a
  have hx : 0 < x := by
    dsimp [x]
    exact one_div_pos.mpr ha
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (div_le_iff₀ ha).2 (by simpa using ha1)
  have hden : 0 < a ^ 2 := pow_pos ha 2
  have hfrac : C / (a ^ 2) < 1 := by
    exact (div_lt_iff₀ hden).2 (by simpa using hCa2)
  have hx2eq : x ^ 2 = 1 / (a ^ 2) := by
    dsimp [x]
    field_simp [ne_of_gt ha]
  have hcx2 : C * x ^ 2 < 1 := by
    rw [hx2eq]
    simpa [div_eq_mul_inv] using hfrac
  have hx2pos : 0 < x ^ 2 := pow_pos hx 2
  have hmul : (C * x ^ 2) * x ^ 2 < 1 * x ^ 2 :=
    mul_lt_mul_of_pos_right hcx2 hx2pos
  have hfinal : C * x ^ 4 < x ^ 2 := by
    calc
      C * x ^ 4 = (C * x ^ 2) * x ^ 2 := by ring
      _ < 1 * x ^ 2 := hmul
      _ = x ^ 2 := by ring
  exact ⟨x, hx, hx1, hfinal⟩

/-- No uniform quadratic error bound exists for the quartic defect on `[0,1]`. -/
theorem no_uniform_quadratic_error_bound :
    ¬ ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → x ≤ 1 → x ^ 2 ≤ C * x ^ 4 := by
  rintro ⟨C, hC⟩
  obtain ⟨x, hx, hx1, hbad⟩ := quartic_not_quadratically_coercive C
  exact (not_lt_of_ge (hC x (le_of_lt hx) hx1)) hbad

end QuarticDefect

section SpectralCapacity

/--
Algebraic core of the corrected spectral defect-capacity theorem.

`badSq` is the square-sum contributed by the `k` bad directions; `remSum` and
`remSq` are the sum and square-sum of the remaining directions.  `hcs` is the
finite Cauchy--Schwarz input.  The sign hypothesis is explicit.
-/
theorem defect_capacity_core_mul
    (S M η k n badSq remSum remSq : ℝ)
    (hn : 0 ≤ n)
    (hbad : k * η ^ 2 ≤ badSq)
    (hsum : M + k * η ≤ remSum)
    (hsign : 0 ≤ M + k * η)
    (hcs : remSum ^ 2 ≤ n * remSq)
    (hbudget : badSq + remSq ≤ S) :
    n * (k * η ^ 2) + (M + k * η) ^ 2 ≤ n * S := by
  have hrem : 0 ≤ remSum := le_trans hsign hsum
  have hsq : (M + k * η) ^ 2 ≤ remSum ^ 2 := by
    nlinarith
  have hbadmul : n * (k * η ^ 2) ≤ n * badSq :=
    mul_le_mul_of_nonneg_left hbad hn
  have hbudgetmul : n * (badSq + remSq) ≤ n * S :=
    mul_le_mul_of_nonneg_left hbudget hn
  nlinarith

/-- Exact algebraic rearrangement to the defect-capacity numerator bound. -/
theorem defect_capacity_rearranged
    (S M η k d n : ℝ)
    (hnrel : n = d - k)
    (hcore : n * (k * η ^ 2) + (M + k * η) ^ 2 ≤ n * S) :
    k * (S + d * η ^ 2 + 2 * M * η) ≤ S * d - M ^ 2 := by
  rw [hnrel] at hcore
  nlinarith [hcore]

/-- Ratio form of the capacity bound when the denominator is positive. -/
theorem defect_capacity_ratio
    (S M η k d n : ℝ)
    (hnrel : n = d - k)
    (hcore : n * (k * η ^ 2) + (M + k * η) ^ 2 ≤ n * S)
    (hden : 0 < S + d * η ^ 2 + 2 * M * η) :
    k ≤ (S * d - M ^ 2) / (S + d * η ^ 2 + 2 * M * η) := by
  apply (le_div_iff₀ hden).2
  exact defect_capacity_rearranged S M η k d n hnrel hcore

/-- Algebraic identity for the sharp one-defect extremal spectrum. -/
theorem one_defect_threshold_identity
    (M η d : ℝ) (hd : 1 < d) :
    η ^ 2 + (d - 1) * ((M + η) / (d - 1)) ^ 2 =
      η ^ 2 + (M + η) ^ 2 / (d - 1) := by
  have hne : d - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hd)
  field_simp [hne]
  ring

end SpectralCapacity

end MillenniumB4
