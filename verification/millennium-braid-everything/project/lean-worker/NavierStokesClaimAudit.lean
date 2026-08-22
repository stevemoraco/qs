import Mathlib

namespace NavierStokesClaimAudit

/-- On the interval `(0,1)`, squaring strictly decreases a nonnegative
critical-size coordinate. This is the scalar obstruction behind replacing
an `L^(3/2)` norm by its square. -/
theorem small_norm_square_gap {x : ℝ}
    (hx : 0 < x) (hx1 : x < 1) :
    x ^ 2 < x := by
  have hprod : 0 < x * (1 - x) :=
    mul_pos hx (sub_pos.mpr hx1)
  nlinarith

/-- More generally, if a fixed coefficient `C` has not yet compensated the
small coordinate `x`, then `C x^2` is strictly smaller than `x`. -/
theorem weighted_square_gap {C x : ℝ}
    (hx : 0 < x) (hCx : C * x < 1) :
    C * x ^ 2 < x := by
  have h := mul_lt_mul_of_pos_right hCx hx
  simpa [pow_two, mul_assoc] using h

/-- Exact indicator-mass certificate used in the source-density audit.
For a set of measure `1/8`, the `L^(3/2)` norm of its indicator is `1/4`,
whereas the square of that norm is `1/16`. -/
theorem indicator_eighth_mass_gap :
    ¬ ((1 / 4 : ℝ) ≤ (1 / 4 : ℝ) ^ 2) := by
  norm_num

/-- Three labels for the finite 2-Helly obstruction. -/
inductive Label
  | a
  | b
  | c
  deriving DecidableEq, Fintype

/-- Three overlapping coherence classes. -/
inductive CoherenceClass
  | ab
  | bc
  | ac
  deriving DecidableEq, Fintype

/-- Membership table for the classes `{a,b}`, `{b,c}`, `{a,c}`. -/
def inClass : Label → CoherenceClass → Bool
  | Label.a, CoherenceClass.ab => true
  | Label.b, CoherenceClass.ab => true
  | Label.b, CoherenceClass.bc => true
  | Label.c, CoherenceClass.bc => true
  | Label.a, CoherenceClass.ac => true
  | Label.c, CoherenceClass.ac => true
  | _, _ => false

/-- Every pair of labels lies in some coherence class, but no single class
contains all three labels. Thus pairwise non-separation does not imply
support in one class without an additional 2-Helly/laminarity theorem. -/
theorem pairwise_shared_without_global_class :
    (∀ x y : Label, ∃ K : CoherenceClass,
      inClass x K = true ∧ inClass y K = true) ∧
    ¬ (∃ K : CoherenceClass, ∀ x : Label, inClass x K = true) := by
  decide

#print axioms small_norm_square_gap
#print axioms weighted_square_gap
#print axioms indicator_eighth_mass_gap
#print axioms pairwise_shared_without_global_class

end NavierStokesClaimAudit
