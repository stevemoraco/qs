import Mathlib

/-!
# MCSP dummy-padding parameter obstruction

Finite arithmetic core only. This does not prove or disprove P vs NP.
If `0 < μ₁ < μ₂`, `n > 0`, and `r ≥ 0`, then padding from `n` to
`n+r` variables makes the larger exponent threshold `μ₂(n+r)` strictly
larger than the desired `μ₁ n` threshold.
-/

namespace Millennium
namespace PNPMcspPaddingNoGo

/-- Dummy-variable padding cannot shrink a larger MCSP exponent parameter. -/
theorem exponent_gap_grows_under_padding
    (μ₁ μ₂ n r : ℝ)
    (hμ : μ₁ < μ₂)
    (hn : 0 < n)
    (hr : 0 ≤ r)
    (hμ₂ : 0 ≤ μ₂) :
    μ₁ * n < μ₂ * (n + r) := by
  have hbase : μ₁ * n < μ₂ * n := by
    exact mul_lt_mul_of_pos_right hμ hn
  have hpad : μ₂ * n ≤ μ₂ * (n + r) := by
    exact mul_le_mul_of_nonneg_left (by linarith) hμ₂
  exact lt_of_lt_of_le hbase hpad

end PNPMcspPaddingNoGo
end Millennium
