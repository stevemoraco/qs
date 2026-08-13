import Mathlib

/-!
# Hodge lane: outer-product Diophantine firewall

This file isolates an arithmetic obstruction with no geometric input.

The factor equation
`(3a+1)(3b+1)=52`
has, up to exchanging `a,b`, only the pairs
`(0,17)`, `(-1,-9)`, and `(1,4)`.

The corresponding monic cubics are

* `z^3 - 18z^2 + 29z - 208`;
* `z^3 + 9z^2 + 11z + 107`;
* `z^3 - 6z^2 + 21z - 68`.

The first two have no integer root modulo three; the third has no
integer root modulo five.

This is only a finite Diophantine certificate. It does not formalize the
geometric derivation of the factor equation or cubics, semiregularity,
or the Hodge conjecture.
-/

namespace Millennium.Hodge.OuterProductArithmetic

/-- The factor equation has exactly six ordered solutions, or three
solutions up to exchanging the variables. -/
theorem factor_pair_classification {a b : ℤ}
    (h : (3 * a + 1) * (3 * b + 1) = 52) :
    (a = 0 ∧ b = 17) ∨ (a = 17 ∧ b = 0) ∨
    (a = -1 ∧ b = -9) ∨ (a = -9 ∧ b = -1) ∨
    (a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1) := by
  have hdiv : 3 * a + 1 ∣ (52 : ℤ) := by
    refine ⟨3 * b + 1, ?_⟩
    exact h.symm
  have habs : (3 * a + 1).natAbs ≤ (52 : ℤ).natAbs :=
    Int.natAbs_le_of_dvd_ne_zero hdiv (by norm_num)
  have hsq : (3 * a + 1) * (3 * a + 1) ≤ (52 : ℤ) * 52 :=
    Int.natAbs_le_iff_mul_self_le.mp habs
  have hlow : (-18 : ℤ) < a := by
    nlinarith [sq_nonneg ((3 * a + 1) + 52)]
  have hhigh : a < 18 := by
    nlinarith [sq_nonneg ((3 * a + 1) - 52)]
  interval_cases a <;> norm_num at h ⊢ <;> omega

/-- The three corresponding cubics have no integer roots. The first
two contradictions are computed in `ZMod 3`, and the third in
`ZMod 5`. -/
theorem corresponding_cubics_have_no_integer_roots :
    (¬ ∃ z : ℤ, z ^ 3 - 18 * z ^ 2 + 29 * z - 208 = 0) ∧
    (¬ ∃ z : ℤ, z ^ 3 + 9 * z ^ 2 + 11 * z + 107 = 0) ∧
    (¬ ∃ z : ℤ, z ^ 3 - 6 * z ^ 2 + 21 * z - 68 = 0) := by
  constructor
  · rintro ⟨z, hz⟩
    let r : ℤ := z % 3
    have hr0 : 0 ≤ r := by
      dsimp [r]
      exact Int.emod_nonneg z (by norm_num)
    have hrlt : r < 3 := by
      dsimp [r]
      exact Int.emod_lt_of_pos z (by norm_num)
    have hrz : r ≡ z [ZMOD 3] := by
      simp [Int.ModEq, r]
    have H : r ^ 3 - 18 * r ^ 2 + 29 * r - 208 ≡ 0 [ZMOD 3] := calc
      _ ≡ z ^ 3 - 18 * z ^ 2 + 29 * z - 208 [ZMOD 3] := by gcongr
      _ = 0 := hz
    interval_cases r <;> norm_num [Int.ModEq] at H
  constructor
  · rintro ⟨z, hz⟩
    let r : ℤ := z % 3
    have hr0 : 0 ≤ r := by
      dsimp [r]
      exact Int.emod_nonneg z (by norm_num)
    have hrlt : r < 3 := by
      dsimp [r]
      exact Int.emod_lt_of_pos z (by norm_num)
    have hrz : r ≡ z [ZMOD 3] := by
      simp [Int.ModEq, r]
    have H : r ^ 3 + 9 * r ^ 2 + 11 * r + 107 ≡ 0 [ZMOD 3] := calc
      _ ≡ z ^ 3 + 9 * z ^ 2 + 11 * z + 107 [ZMOD 3] := by gcongr
      _ = 0 := hz
    interval_cases r <;> norm_num [Int.ModEq] at H
  · rintro ⟨z, hz⟩
    let r : ℤ := z % 5
    have hr0 : 0 ≤ r := by
      dsimp [r]
      exact Int.emod_nonneg z (by norm_num)
    have hrlt : r < 5 := by
      dsimp [r]
      exact Int.emod_lt_of_pos z (by norm_num)
    have hrz : r ≡ z [ZMOD 5] := by
      simp [Int.ModEq, r]
    have H : r ^ 3 - 6 * r ^ 2 + 21 * r - 68 ≡ 0 [ZMOD 5] := calc
      _ ≡ z ^ 3 - 6 * z ^ 2 + 21 * z - 68 [ZMOD 5] := by gcongr
      _ = 0 := hz
    interval_cases r <;> norm_num [Int.ModEq] at H

/-- Combined arithmetic no-go: every solution of the factor equation is
one of the three unordered pairs, and none of its corresponding cubics
can have an integer root. -/
theorem classified_outer_product_no_go {a b : ℤ}
    (h : (3 * a + 1) * (3 * b + 1) = 52) :
    ((a = 0 ∧ b = 17) ∨ (a = 17 ∧ b = 0) ∨
      (a = -1 ∧ b = -9) ∨ (a = -9 ∧ b = -1) ∨
      (a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1)) ∧
    (¬ ∃ z : ℤ, z ^ 3 - 18 * z ^ 2 + 29 * z - 208 = 0) ∧
    (¬ ∃ z : ℤ, z ^ 3 + 9 * z ^ 2 + 11 * z + 107 = 0) ∧
    (¬ ∃ z : ℤ, z ^ 3 - 6 * z ^ 2 + 21 * z - 68 = 0) := by
  exact ⟨factor_pair_classification h,
    corresponding_cubics_have_no_integer_roots⟩

#print axioms factor_pair_classification
#print axioms corresponding_cubics_have_no_integer_roots
#print axioms classified_outer_product_no_go

end Millennium.Hodge.OuterProductArithmetic
