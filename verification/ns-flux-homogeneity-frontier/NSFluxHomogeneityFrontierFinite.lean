import Mathlib

namespace NSFluxHomogeneityFrontier

/-- A nonzero cubic response cannot be uniformly bounded by a quadratic
response over every positive amplitude. -/
theorem cubic_not_uniformly_quadratic
    (A C : ℝ)
    (hA : 0 < A)
    (hC : 0 ≤ C) :
    ¬ (∀ x : ℝ, 0 < x → A * x ^ 3 ≤ C * x ^ 2) := by
  intro h
  let x : ℝ := C / A + 1
  have hdiv : 0 ≤ C / A := div_nonneg hC hA.le
  have hx : 0 < x := by
    dsimp [x]
    linarith
  have hAne : A ≠ 0 := ne_of_gt hA
  have hAx : A * x = C + A := by
    dsimp [x]
    field_simp [hAne]
  have hgt : C < A * x := by
    rw [hAx]
    linarith
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
  have hstrict : C * x ^ 2 < A * x ^ 3 := by
    calc
      C * x ^ 2 < (A * x) * x ^ 2 :=
        mul_lt_mul_of_pos_right hgt hx2
      _ = A * x ^ 3 := by ring
  exact (not_lt_of_ge (h x hx)) hstrict

/-- Raising the candidate right-hand side to quartic amplitude degree is not a
uniform repair: it fails at sufficiently small positive amplitude. -/
theorem cubic_not_uniformly_quartic
    (A C : ℝ)
    (hA : 0 < A)
    (hC : 0 ≤ C) :
    ¬ (∀ x : ℝ, 0 < x → A * x ^ 3 ≤ C * x ^ 4) := by
  intro h
  let d : ℝ := 2 * (C + 1)
  let x : ℝ := A / d
  have hd : 0 < d := by
    dsimp [d]
    nlinarith
  have hx : 0 < x := div_pos hA hd
  have hratio : C / d < 1 := by
    apply (div_lt_one hd).2
    dsimp [d]
    nlinarith
  have hClt : C * x < A := by
    calc
      C * x = A * (C / d) := by
        dsimp [x]
        ring
      _ < A * 1 := mul_lt_mul_of_pos_left hratio hA
      _ = A := by ring
  have hx3 : 0 < x ^ 3 := pow_pos hx 3
  have hstrict : C * x ^ 4 < A * x ^ 3 := by
    calc
      C * x ^ 4 = (C * x) * x ^ 3 := by ring
      _ < A * x ^ 3 := mul_lt_mul_of_pos_right hClt hx3
  exact (not_lt_of_ge (h x hx)) hstrict

/-- Linear growth in the modulation frequency cannot be uniformly bounded by
inverse-frequency decay. -/
theorem linear_not_uniformly_inverse
    (A C : ℝ)
    (hA : 0 < A)
    (hC : 0 ≤ C) :
    ¬ (∀ n : ℝ, 0 < n → A * n ≤ C / n) := by
  intro h
  let n : ℝ := C / A + 1
  have hdiv : 0 ≤ C / A := div_nonneg hC hA.le
  have hn : 0 < n := by
    dsimp [n]
    linarith
  have hn1 : 1 ≤ n := by
    dsimp [n]
    linarith
  have hAne : A ≠ 0 := ne_of_gt hA
  have hAn : A * n = C + A := by
    dsimp [n]
    field_simp [hAne]
  have hAnC : C < A * n := by
    rw [hAn]
    linarith
  have hAnpos : 0 < A * n := mul_pos hA hn
  have hmono : A * n ≤ (A * n) * n := by
    have hprod : 0 ≤ (A * n) * (n - 1) :=
      mul_nonneg hAnpos.le (sub_nonneg.mpr hn1)
    nlinarith
  have hcross : (A * n) * n ≤ C :=
    (le_div_iff₀ hn).mp (h n hn)
  linarith

/-- The exact Pavesi-type two-axis shape `A*n*x^3 ≤ C*x^2/n`
cannot hold with one nonnegative universal constant. -/
theorem pavesi_two_axis_no_constant
    (A : ℝ)
    (hA : 0 < A) :
    ¬ (∃ C : ℝ,
      0 ≤ C ∧
      ∀ n x : ℝ,
        0 < n → 0 < x →
        A * n * x ^ 3 ≤ C * x ^ 2 / n) := by
  rintro ⟨C, hC, hbound⟩
  apply cubic_not_uniformly_quadratic A C hA hC
  intro x hx
  have h1 := hbound 1 x (by norm_num) hx
  simpa using h1

/-- The two independent exponent deficits in the advertised estimate are
exactly one missing amplitude power and two missing frequency powers. -/
theorem pavesi_ratio_scaling_identity
    (A n x : ℝ) :
    (A * n * x ^ 3) * n = A * n ^ 2 * x * x ^ 2 := by
  ring

#print axioms cubic_not_uniformly_quadratic
#print axioms cubic_not_uniformly_quartic
#print axioms linear_not_uniformly_inverse
#print axioms pavesi_two_axis_no_constant
#print axioms pavesi_ratio_scaling_identity

end NSFluxHomogeneityFrontier
