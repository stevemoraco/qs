import Mathlib

/-!
# Order-theoretic core of the Navier--Stokes packet-minimality audit

A canonical order whose primary continuous coordinate is a strictly positive
parabolic scale ordered by "smaller scale first" is not well-founded merely
from positivity: the positive reals have no least element.

This is only the finite/order core of the audit; no PDE statement is encoded.
-/

namespace NavierStokesBraid

/-- Every positive scale admits a strictly smaller positive half-scale. -/
theorem positive_half_is_smaller (r : ℝ) (hr : 0 < r) :
    0 < r / 2 ∧ r / 2 < r := by
  constructor <;> linarith

/-- There is no least strictly positive real scale. -/
theorem no_least_positive_real_scale :
    ¬ ∃ r : ℝ, 0 < r ∧ ∀ s : ℝ, 0 < s → r ≤ s := by
  rintro ⟨r, hr, hleast⟩
  have hhalf := positive_half_is_smaller r hr
  have hle : r ≤ r / 2 := hleast (r / 2) hhalf.1
  linarith

end NavierStokesBraid
