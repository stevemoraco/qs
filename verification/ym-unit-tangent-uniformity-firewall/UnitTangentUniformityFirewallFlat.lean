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

#print axioms normalized_unitTangent_conjugacy_quartic
#print axioms normalized_unitTangent_quartic_unbounded
#print axioms no_uniform_quartic_bound_from_unitTangent_alone

end Millennium.YangMills
