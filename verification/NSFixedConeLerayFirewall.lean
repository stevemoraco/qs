import Mathlib

namespace Millennium.NavierStokes.FixedConeLerayFirewall

theorem cone_contains_real_line
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : V → Prop)
    (hscale : ∀ {a : ℝ} {v : V}, 0 ≤ a → C v → C (a • v))
    {x : V} (hx : C x) (hneg : C (-x)) :
    ∀ a : ℝ, C (a • x) := by
  intro a
  by_cases ha : 0 ≤ a
  · exact hscale ha hx
  · have hna : 0 ≤ -a := neg_nonneg.mpr (le_of_not_ge ha)
    have h := hscale (a := -a) (v := -x) hna hneg
    simpa using h

abbrev Triple := ℝ × (ℝ × ℝ)

def leray11 (x : Triple) : Triple :=
  ((x.1 - x.2.1) / 2, ((-x.1 + x.2.1) / 2, x.2.2))

theorem leray11_idempotent (x : Triple) :
    leray11 (leray11 x) = leray11 x := by
  rcases x with ⟨x, y, z⟩
  ext <;> simp [leray11] <;> ring

theorem leray11_annihilates_frequency :
    leray11 (1, (1, 0)) = (0, (0, 0)) := by
  norm_num [leray11]

def PositiveOrthant (x : Triple) : Prop :=
  0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2

theorem firstAxis_positive : PositiveOrthant (1, (0, 0)) := by
  norm_num [PositiveOrthant]

theorem leray11_firstAxis :
    leray11 (1, (0, 0)) = ((1 : ℝ) / 2, ((-1 : ℝ) / 2, 0)) := by
  norm_num [leray11]

theorem leray11_does_not_preserve_positiveOrthant :
    ¬ PositiveOrthant (leray11 (1, (0, 0))) := by
  norm_num [PositiveOrthant, leray11]

#print axioms cone_contains_real_line
#print axioms leray11_idempotent
#print axioms leray11_annihilates_frequency
#print axioms firstAxis_positive
#print axioms leray11_firstAxis
#print axioms leray11_does_not_preserve_positiveOrthant

end Millennium.NavierStokes.FixedConeLerayFirewall
