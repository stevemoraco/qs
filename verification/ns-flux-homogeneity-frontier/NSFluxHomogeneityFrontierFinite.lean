import Mathlib

namespace NSFluxHomogeneityFrontier

/-- A nonzero cubic response cannot be uniformly bounded by a quadratic
response over every positive amplitude. -/
theorem cubic_not_uniformly_quadratic
    (A C : ℝ)
    (hA : 0 < A)
    (hC : 0 ≤ C) :
    ¬ (∀ λ : ℝ, 0 < λ → A * λ ^ 3 ≤ C * λ ^ 2) := by
  intro h
  let λ : ℝ := C / A + 1
  have hdiv : 0 ≤ C / A := div_nonneg hC hA.le
  have hλ : 0 < λ := by
    dsimp [λ]
    linarith
  have hAne : A ≠ 0 := ne_of_gt hA
  have hAlam : A * λ = C + A := by
    dsimp [λ]
    field_simp [hAne]
    <;> ring
  have hgt : C < A * λ := by
    rw [hAlam]
    linarith
  have hλ2 : 0 < λ ^ 2 := sq_pos_of_pos hλ
  have hstrict : C * λ ^ 2 < A * λ ^ 3 := by
    calc
      C * λ ^ 2 < (A * λ) * λ ^ 2 :=
        mul_lt_mul_of_pos_right hgt hλ2
      _ = A * λ ^ 3 := by ring
  exact (not_lt_of_ge (h λ hλ)) hstrict

/-- Raising the candidate right-hand side to quartic amplitude degree is not a
uniform repair: it fails at sufficiently small positive amplitude. -/
theorem cubic_not_uniformly_quartic
    (A C : ℝ)
    (hA : 0 < A)
    (hC : 0 ≤ C) :
    ¬ (∀ λ : ℝ, 0 < λ → A * λ ^ 3 ≤ C * λ ^ 4) := by
  intro h
  let d : ℝ := 2 * (C + 1)
  let λ : ℝ := A / d
  have hd : 0 < d := by
    dsimp [d]
    nlinarith
  have hλ : 0 < λ := div_pos hA hd
  have hratio : C / d < 1 := by
    apply (div_lt_one hd).2
    dsimp [d]
    nlinarith
  have hClt : C * λ < A := by
    calc
      C * λ = A * (C / d) := by
        dsimp [λ]
        ring
      _ < A * 1 := mul_lt_mul_of_pos_left hratio hA
      _ = A := by ring
  have hλ3 : 0 < λ ^ 3 := pow_pos hλ 3
  have hstrict : C * λ ^ 4 < A * λ ^ 3 := by
    calc
      C * λ ^ 4 = (C * λ) * λ ^ 3 := by ring
      _ < A * λ ^ 3 := mul_lt_mul_of_pos_right hClt hλ3
  exact (not_lt_of_ge (h λ hλ)) hstrict

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
    <;> ring
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

/-- The exact Pavesi-type two-axis shape `A*n*λ^3 ≤ C*λ^2/n`
cannot hold with one nonnegative universal constant. -/
theorem pavesi_two_axis_no_constant
    (A : ℝ)
    (hA : 0 < A) :
    ¬ (∃ C : ℝ,
      0 ≤ C ∧
      ∀ n λ : ℝ,
        0 < n → 0 < λ →
        A * n * λ ^ 3 ≤ C * λ ^ 2 / n) := by
  rintro ⟨C, hC, hbound⟩
  apply cubic_not_uniformly_quadratic A C hA hC
  intro λ hλ
  have h1 := hbound 1 λ (by norm_num) hλ
  simpa using h1

/-- The two independent exponent deficits in the advertised estimate are
exactly one missing amplitude power and two missing frequency powers. -/
theorem pavesi_ratio_scaling_identity
    (A C n λ : ℝ) :
    (A * n * λ ^ 3) * n = A * n ^ 2 * λ * λ ^ 2 := by
  ring

#print axioms cubic_not_uniformly_quadratic
#print axioms cubic_not_uniformly_quartic
#print axioms linear_not_uniformly_inverse
#print axioms pavesi_two_axis_no_constant
#print axioms pavesi_ratio_scaling_identity

end NSFluxHomogeneityFrontier
