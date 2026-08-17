import Mathlib

/-!
# Joint Cauchy ledger for selected source roots

The analytic input intended upstream is a joint field/source holomorphic tube.
Cauchy in the selected source variables contributes

  `s! * sourceInvRadius^s`

at source order `s`; Cauchy/polarization in the field variable contributes

  `q! * fieldRate^q`

at arbitrary incident field degree `q` after one fixed radius loss.  Since the
prize-facing root order is at most two, the complete source factor is bounded
by one constant independent of `q`.

This file formalizes only that finite rate algebra.  It does not formalize
Banach holomorphy, Cauchy estimates, replica--BKAR, Kirk's source activities,
Yang--Mills theory, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.JointCauchyRootDegreeLedger

/-- At source order at most two, factorial Cauchy loss is one fixed square
factor. -/
theorem source_order_at_most_two_fixed_factor
    (s : ℕ) (a : ℝ) (ha : 0 ≤ a) (hs : s ≤ 2) :
    (s.factorial : ℝ) * a ^ s ≤ 2 * (max 1 a) ^ 2 := by
  have hM1 : 1 ≤ max 1 a := le_max_left 1 a
  have haM : a ≤ max 1 a := le_max_right 1 a
  have hM0 : 0 ≤ max 1 a := le_trans (by norm_num) hM1
  rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with rfl | rfl | rfl
  · norm_num
    nlinarith [sq_nonneg (max 1 a - 1)]
  · simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one]
    have hsq : a ^ 2 ≤ (max 1 a) ^ 2 := by
      nlinarith [sq_nonneg (max 1 a - a)]
    nlinarith
  · norm_num [Nat.factorial]
    nlinarith [sq_nonneg (max 1 a - a)]

/-- A mixed field/source Cauchy row with source order at most two reduces to
one arbitrary-field-degree species row with a root constant independent of
that degree. -/
theorem mixed_cauchy_row_to_degree_uniform_root_row
    (q s : ℕ)
    (coeff M fieldRate sourceInvRadius : ℝ)
    (hM : 0 ≤ M)
    (hfield : 0 ≤ fieldRate)
    (hsource : 0 ≤ sourceInvRadius)
    (hs : s ≤ 2)
    (hcoeff :
      coeff ≤
        M * (q.factorial : ℝ) * fieldRate ^ q *
          ((s.factorial : ℝ) * sourceInvRadius ^ s)) :
    coeff ≤
      (2 * M * (max 1 sourceInvRadius) ^ 2) *
        (q.factorial : ℝ) * fieldRate ^ q := by
  have hsourceFactor :=
    source_order_at_most_two_fixed_factor s sourceInvRadius hsource hs
  have hqfact : 0 ≤ (q.factorial : ℝ) := by positivity
  have hfieldPow : 0 ≤ fieldRate ^ q := pow_nonneg hfield q
  have hleft : 0 ≤ M * (q.factorial : ℝ) * fieldRate ^ q := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsourceFactor hleft
  calc
    coeff ≤
        M * (q.factorial : ℝ) * fieldRate ^ q *
          ((s.factorial : ℝ) * sourceInvRadius ^ s) := hcoeff
    _ ≤
        M * (q.factorial : ℝ) * fieldRate ^ q *
          (2 * (max 1 sourceInvRadius) ^ 2) := hscaled
    _ =
        (2 * M * (max 1 sourceInvRadius) ^ 2) *
          (q.factorial : ℝ) * fieldRate ^ q := by ring

/-- Two independent selected source directions with individual inverse-radius
rates are paid by one fixed product constant, again independent of arbitrary
field degree. -/
theorem two_direction_mixed_row
    (q : ℕ)
    (coeff M fieldRate sourceRate₁ sourceRate₂ : ℝ)
    (hM : 0 ≤ M)
    (hfield : 0 ≤ fieldRate)
    (hs1 : 0 ≤ sourceRate₁)
    (hs2 : 0 ≤ sourceRate₂)
    (hcoeff :
      coeff ≤
        M * (q.factorial : ℝ) * fieldRate ^ q *
          sourceRate₁ * sourceRate₂) :
    coeff ≤
      (M * max 1 sourceRate₁ * max 1 sourceRate₂) *
        (q.factorial : ℝ) * fieldRate ^ q := by
  have h1 : sourceRate₁ ≤ max 1 sourceRate₁ := le_max_right 1 sourceRate₁
  have h2 : sourceRate₂ ≤ max 1 sourceRate₂ := le_max_right 1 sourceRate₂
  have hM1 : 0 ≤ max 1 sourceRate₁ := by
    exact le_trans (by norm_num) (le_max_left 1 sourceRate₁)
  have hM2 : 0 ≤ max 1 sourceRate₂ := by
    exact le_trans (by norm_num) (le_max_left 1 sourceRate₂)
  have hp :
      sourceRate₁ * sourceRate₂ ≤
        max 1 sourceRate₁ * max 1 sourceRate₂ :=
    mul_le_mul h1 h2 hs2 hM1
  have hleft : 0 ≤ M * (q.factorial : ℝ) * fieldRate ^ q := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hp hleft
  calc
    coeff ≤
        M * (q.factorial : ℝ) * fieldRate ^ q *
          sourceRate₁ * sourceRate₂ := hcoeff
    _ ≤
        M * (q.factorial : ℝ) * fieldRate ^ q *
          (max 1 sourceRate₁ * max 1 sourceRate₂) := by
      simpa [mul_assoc] using hscaled
    _ =
        (M * max 1 sourceRate₁ * max 1 sourceRate₂) *
          (q.factorial : ℝ) * fieldRate ^ q := by ring

/-- Once a field Cauchy/polarization estimate has been rewritten with one
fixed effective field rate, a selected-root constant cannot change its
factorial exponent or its field-degree rate. -/
theorem fixed_root_factor_preserves_species_rate
    (q : ℕ) (rootConst M fieldRate coeff : ℝ)
    (hroot : 0 ≤ rootConst)
    (hM : 0 ≤ M)
    (hfield : 0 ≤ fieldRate)
    (hcoeff :
      coeff ≤ rootConst * (M * (q.factorial : ℝ) * fieldRate ^ q)) :
    coeff ≤
      (rootConst * M) * (q.factorial : ℝ) * fieldRate ^ q := by
  calc
    coeff ≤ rootConst * (M * (q.factorial : ℝ) * fieldRate ^ q) := hcoeff
    _ = (rootConst * M) * (q.factorial : ℝ) * fieldRate ^ q := by ring

#print axioms source_order_at_most_two_fixed_factor
#print axioms mixed_cauchy_row_to_degree_uniform_root_row
#print axioms two_direction_mixed_row
#print axioms fixed_root_factor_preserves_species_rate

end Millennium.YangMills.JointCauchyRootDegreeLedger
