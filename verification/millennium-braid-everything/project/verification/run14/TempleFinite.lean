import Mathlib

namespace MillenniumRun14

/-- Scalar rearrangement at the end of the Temple variance inequality. -/
theorem temple_lower_bound_rearrangement
    (mu eps beta lam : ℝ)
    (hgap : mu < beta)
    (hvar : (mu - lam) * (beta - mu) ≤ eps ^ 2) :
    mu - eps ^ 2 / (beta - mu) ≤ lam := by
  have hpos : 0 < beta - mu := sub_pos.mpr hgap
  have hle : mu - lam ≤ eps ^ 2 / (beta - mu) :=
    (le_div_iff₀ hpos).2 hvar
  linarith

end MillenniumRun14
