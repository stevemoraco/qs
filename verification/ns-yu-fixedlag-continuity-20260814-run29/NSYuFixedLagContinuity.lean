import Mathlib

/-!
# Yu fixed-lag continuity firewall

Finite real algebra only.  These lemmas formalize the exact telescoping estimate
used when a fixed relative-lag filtered work functional is passed through a
strong compactness limit one factor at a time.

They do **not** formalize Navier--Stokes, Yu's filtered operators, Type-I
compactness, ancient solutions, or any Millennium conclusion.
-/

namespace NSYuFixedLagContinuity

/-- Exact three-factor telescoping identity. -/
theorem cubic_difference_identity
    (a b c x y z : ℝ) :
    a * b * c - x * y * z =
      (a - x) * b * c + x * (b - y) * c + x * y * (c - z) := by
  ring

/-- If the three telescoping pieces of a cubic work functional have error
budgets `e₁,e₂,e₃`, their total work error is at most the sum of those budgets. -/
theorem cubic_difference_abs_budget
    (a b c x y z e₁ e₂ e₃ : ℝ)
    (h₁ : |(a - x) * b * c| ≤ e₁)
    (h₂ : |x * (b - y) * c| ≤ e₂)
    (h₃ : |x * y * (c - z)| ≤ e₃) :
    |a * b * c - x * y * z| ≤ e₁ + e₂ + e₃ := by
  calc
    |a * b * c - x * y * z| =
        |((a - x) * b * c + x * (b - y) * c) + x * y * (c - z)| := by
          rw [cubic_difference_identity]
    _ ≤ |(a - x) * b * c + x * (b - y) * c| + |x * y * (c - z)| :=
      abs_add_le _ _
    _ ≤ (|(a - x) * b * c| + |x * (b - y) * c|) + |x * y * (c - z)| := by
      exact add_le_add_right (abs_add_le _ _) _
    _ ≤ e₁ + e₂ + e₃ := by
      linarith

/-- A positive work floor survives a limit once the total work error is at most
half of that floor. -/
theorem positive_work_survives_half_error
    (ε oldWork newWork : ℝ)
    (hε : 0 ≤ ε)
    (hold : ε ≤ oldWork)
    (herr : |oldWork - newWork| ≤ ε / 2) :
    ε / 2 ≤ newWork := by
  have hlower : -(ε / 2) ≤ oldWork - newWork := (abs_le.mp herr).1
  linarith

/-- With a strictly positive original floor, the retained half-floor is also
strictly positive. -/
theorem positive_work_remains_strict
    (ε oldWork newWork : ℝ)
    (hε : 0 < ε)
    (hold : ε ≤ oldWork)
    (herr : |oldWork - newWork| ≤ ε / 2) :
    0 < newWork := by
  have hhalf : ε / 2 ≤ newWork :=
    positive_work_survives_half_error ε oldWork newWork (le_of_lt hε) hold herr
  linarith

#print axioms cubic_difference_identity
#print axioms cubic_difference_abs_budget
#print axioms positive_work_survives_half_error
#print axioms positive_work_remains_strict

end NSYuFixedLagContinuity
