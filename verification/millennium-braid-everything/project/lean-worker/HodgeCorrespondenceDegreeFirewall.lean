import Mathlib

namespace HodgeCorrespondenceDegreeFirewall

/-- For a positive Lefschetz power `r`, the codimensions needed for a
correspondence of degree `+r` and one of degree `-r` are different. -/
theorem positive_and_negative_correspondence_codim_differ
    {n r : ℤ} (hr : 0 < r) : n + r ≠ n - r := by
  linarith

/-- Scalar normalization cannot repair the grading mismatch: the arithmetic
identity needed to equate the two codimensions forces `r=0`. -/
theorem equal_codim_forces_zero_degree
    {n r : ℤ} (h : n + r = n - r) : r = 0 := by
  linarith

#print axioms positive_and_negative_correspondence_codim_differ
#print axioms equal_codim_forces_zero_degree

end HodgeCorrespondenceDegreeFirewall
