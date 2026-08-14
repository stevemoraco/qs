import Mathlib

namespace Millennium.YangMills

structure ParabolicJet4 where
  quad : ℝ
  cubic : ℝ
  quartic : ℝ

@[ext]
theorem parabolicJet4_ext {x y : ParabolicJet4}
    (hquad : x.quad = y.quad)
    (hcubic : x.cubic = y.cubic)
    (hquartic : x.quartic = y.quartic) : x = y := by
  rcases x with ⟨xq, xc, xk⟩
  rcases y with ⟨yq, yc, yk⟩
  simp_all

def parabolicJet4Comp (outer inner : ParabolicJet4) : ParabolicJet4 where
  quad := outer.quad + inner.quad
  cubic := outer.cubic + inner.cubic + 2 * outer.quad * inner.quad
  quartic :=
    outer.quartic + inner.quartic
      + outer.quad * inner.quad^2
      + 2 * outer.quad * inner.cubic
      + 3 * inner.quad * outer.cubic

def parabolicJet4Inv (j : ParabolicJet4) : ParabolicJet4 where
  quad := -j.quad
  cubic := 2 * j.quad^2 - j.cubic
  quartic := -5 * j.quad^3 + 5 * j.quad * j.cubic - j.quartic

theorem unitTangent_conjugacy_fourJet_formula
    (a d e b c k : ℝ) :
    parabolicJet4Comp
      { quad := a, cubic := d, quartic := e }
      (parabolicJet4Comp
        { quad := b, cubic := c, quartic := k }
        (parabolicJet4Inv { quad := a, cubic := d, quartic := e })) =
      { quad := b,
        cubic := c,
        quartic := k + a * b^2 - a^2 * b - a * c + b * d } := by
  apply parabolicJet4_ext
  · simp [parabolicJet4Comp, parabolicJet4Inv]
  · simp [parabolicJet4Comp, parabolicJet4Inv]
    ring
  · simp [parabolicJet4Comp, parabolicJet4Inv]
    ring

theorem normalized_unitTangent_conjugacy_quartic (a : ℝ) :
    (parabolicJet4Comp
      { quad := a, cubic := 0, quartic := 0 }
      (parabolicJet4Comp
        { quad := 1, cubic := 0, quartic := 0 }
        (parabolicJet4Inv { quad := a, cubic := 0, quartic := 0 }))).quartic =
      a - a^2 := by
  have h := unitTangent_conjugacy_fourJet_formula a 0 0 1 0 0
  simpa using congrArg ParabolicJet4.quartic h

theorem normalized_unitTangent_quartic_unbounded
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ a : ℝ,
      C <
        |(parabolicJet4Comp
          { quad := a, cubic := 0, quartic := 0 }
          (parabolicJet4Comp
            { quad := 1, cubic := 0, quartic := 0 }
            (parabolicJet4Inv
              { quad := a, cubic := 0, quartic := 0 }))).quartic| := by
  refine ⟨C + 2, ?_⟩
  rw [normalized_unitTangent_conjugacy_quartic]
  have hneg : C + 2 - (C + 2)^2 < 0 := by
    nlinarith [sq_nonneg C]
  rw [abs_of_neg hneg]
  nlinarith [sq_nonneg C]

theorem no_uniform_quartic_bound_from_unitTangent_alone :
    ¬ ∃ C : ℝ, 0 ≤ C ∧
      ∀ a : ℝ,
        |(parabolicJet4Comp
          { quad := a, cubic := 0, quartic := 0 }
          (parabolicJet4Comp
            { quad := 1, cubic := 0, quartic := 0 }
            (parabolicJet4Inv
              { quad := a, cubic := 0, quartic := 0 }))).quartic| ≤ C := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨a, ha⟩ := normalized_unitTangent_quartic_unbounded C hC
  exact (not_lt_of_ge (hbound a)) ha

theorem quartic_drift_abs_le_of_low_jet_bounds
    (a d b c A D B C : ℝ)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (ha : |a| ≤ A) (hd : |d| ≤ D) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a * b^2 - a^2 * b - a * c + b * d|
      ≤ A * B^2 + A^2 * B + A * C + B * D := by
  have hb2 : |b|^2 ≤ B^2 :=
    pow_le_pow_left₀ (abs_nonneg b) hb 2
  have ha2 : |a|^2 ≤ A^2 :=
    pow_le_pow_left₀ (abs_nonneg a) ha 2
  have h1 : |a| * |b|^2 ≤ A * B^2 :=
    mul_le_mul ha hb2 (sq_nonneg |b|) hA0
  have h2 : |a|^2 * |b| ≤ A^2 * B :=
    mul_le_mul ha2 hb (abs_nonneg b) (sq_nonneg A)
  have h3 : |a| * |c| ≤ A * C :=
    mul_le_mul ha hc (abs_nonneg c) hA0
  have h4 : |b| * |d| ≤ B * D :=
    mul_le_mul hb hd (abs_nonneg d) hB0
  have hre :
      a * b^2 - a^2 * b - a * c + b * d =
        a * b^2 + (-(a^2 * b)) + (-(a * c)) + b * d := by
    ring
  rw [hre]
  calc
    |a * b^2 + (-(a^2 * b)) + (-(a * c)) + b * d|
        ≤ |a * b^2 + (-(a^2 * b)) + (-(a * c))| + |b * d| :=
          abs_add_le _ _
    _ ≤ (|a * b^2 + (-(a^2 * b))| + |-(a * c)|) + |b * d| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ ((|a * b^2| + |-(a^2 * b)|) + |-(a * c)|) + |b * d| := by
          gcongr
          exact abs_add_le _ _
    _ = |a| * |b|^2 + |a|^2 * |b| + |a| * |c| + |b| * |d| := by
          simp [abs_mul, abs_pow]
    _ ≤ A * B^2 + A^2 * B + A * C + B * D := by
          linarith

#print axioms normalized_unitTangent_conjugacy_quartic
#print axioms normalized_unitTangent_quartic_unbounded
#print axioms no_uniform_quartic_bound_from_unitTangent_alone
#print axioms quartic_drift_abs_le_of_low_jet_bounds

end Millennium.YangMills
