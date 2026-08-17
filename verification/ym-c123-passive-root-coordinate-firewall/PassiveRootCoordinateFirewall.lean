import Mathlib

/-!
# Passive-root coordinate firewall

The Kirk-v4 source audit distinguishes active structural marks, passive source
marks, and passive exterior roots.  A bound on one coordinate cannot be
silently retyped as a bound on an independent passive-root coordinate.

This file gives the minimal real-product countermodel.  It is a typing
firewall only.  It does not formalize Kirk's rooted Banach spaces, replica--BKAR,
renormalization group maps, Yang--Mills theory, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.PassiveRootCoordinateFirewall

/-- Toy seminorm for the already-controlled structural/source coordinate. -/
def structuralSeminorm (x : ℝ × ℝ) : ℝ := |x.1|

/-- Toy seminorm for the distinct passive-root coordinate. -/
def passiveRootSeminorm (x : ℝ × ℝ) : ℝ := |x.2|

/-- For every proposed passive-root bound, there is an element whose
structural coordinate is exactly zero but whose passive-root coordinate exceeds
that bound. -/
theorem independent_passive_root_coordinate (C : ℝ) :
    ∃ x : ℝ × ℝ,
      structuralSeminorm x = 0 ∧ C < passiveRootSeminorm x := by
  refine ⟨(0, |C| + 1), ?_, ?_⟩
  · simp [structuralSeminorm]
  · have hnonneg : 0 ≤ |C| + 1 := by positivity
    have hC : C ≤ |C| := le_abs_self C
    simp only [passiveRootSeminorm]
    rw [abs_of_nonneg hnonneg]
    linarith

/-- A uniform bound on the structural coordinate, even the exact bound zero,
does not imply any uniform bound on the distinct passive-root coordinate. -/
theorem structural_control_does_not_imply_uniform_passive_root_control
    (B : ℝ) (hB : 0 ≤ B) :
    ¬ ∃ C : ℝ, ∀ x : ℝ × ℝ,
      structuralSeminorm x ≤ B → passiveRootSeminorm x ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨x, hxzero, hxlarge⟩ := independent_passive_root_coordinate C
  have hxB : structuralSeminorm x ≤ B := by
    rw [hxzero]
    exact hB
  exact (not_lt_of_ge (hC x hxB)) hxlarge

#print axioms independent_passive_root_coordinate
#print axioms structural_control_does_not_imply_uniform_passive_root_control

end Millennium.YangMills.PassiveRootCoordinateFirewall
