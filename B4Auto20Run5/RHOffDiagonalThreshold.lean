import Mathlib

namespace B4Auto20Run5

/-- BANKER: if a signed off-diagonal term `O` closes a total budget `D + O ≤ B`
and one also has an absolute estimate `|O| ≤ ε`, then the absolute estimate must
be at least as large as the diagonal excess `D - B`. This is the exact scalar
threshold a fixed-block RH energy argument has to pay. -/
theorem rh_absolute_offdiag_bound_must_cover_excess
    (D O B ε : ℝ) (hbudget : D + O ≤ B) (hab : |O| ≤ ε) :
    D - B ≤ ε := by
  have hlow : -ε ≤ O := (abs_le.mp hab).1
  linarith

/-- CRITIC: therefore an absolute off-diagonal estimate that is strictly smaller
than the diagonal excess makes the target budget impossible, regardless of any
other interpretation of the terms. -/
theorem rh_too_small_absolute_offdiag_bound_blocks_budget
    (D O B ε : ℝ) (hexcess : ε < D - B) (hab : |O| ≤ ε) :
    ¬ D + O ≤ B := by
  intro hbudget
  have hneed := rh_absolute_offdiag_bound_must_cover_excess D O B ε hbudget hab
  linarith

/-- CLEANER: the threshold is sharp. Taking the extremal signed cancellation
`O = B - D` exactly meets the budget, and when `B ≤ D` its magnitude is exactly
the diagonal excess `D - B`. -/
theorem rh_excess_threshold_is_sharp
    (D B : ℝ) (hBD : B ≤ D) :
    let O := B - D
    D + O = B ∧ |O| = D - B := by
  dsimp
  constructor
  · ring
  · rw [abs_of_nonpos]
    · ring
    · linarith

#print axioms B4Auto20Run5.rh_absolute_offdiag_bound_must_cover_excess
#print axioms B4Auto20Run5.rh_too_small_absolute_offdiag_bound_blocks_budget
#print axioms B4Auto20Run5.rh_excess_threshold_is_sharp

end B4Auto20Run5
