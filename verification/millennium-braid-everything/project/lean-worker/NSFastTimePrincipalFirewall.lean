import Mathlib

namespace NSFastTimePrincipalFirewall

/-- If the activation exponent beta is strictly larger than twice the carrier exponent b,
then beta - 2b is strictly positive. This is the exponent in Omega/K^2. -/
theorem fast_time_exponent_pos {β b : ℝ} (h : 2 * b < β) : 0 < β - 2 * b := by
  linarith

/-- At the explicit alpha=9/4 parameter point, the fast-time exponent is exactly 1/16. -/
theorem explicit_fast_time_exponent :
    (35 : ℝ) / 16 - 2 * ((17 : ℝ) / 16) = (1 : ℝ) / 16 := by
  norm_num

/-- For a base N>1 and positive exponent d, the nominal WKB temporal ratio N^d exceeds 1. -/
theorem temporal_ratio_gt_one {N d : ℝ} (hN : 1 < N) (hd : 0 < d) :
    1 < N ^ d := by
  exact Real.one_lt_rpow hN hd

/-- Therefore, under beta>2b, a coefficient varying on the activation scale
Omega ~ N^beta cannot satisfy a perturbative Omega/K^2 < 1 criterion
when K ~ N^b and N>1. -/
theorem palasek_activation_not_wkb_small
    {N β b : ℝ}
    (hN : 1 < N)
    (hβ : 2 * b < β) :
    1 < N ^ (β - 2 * b) := by
  exact temporal_ratio_gt_one hN (fast_time_exponent_pos hβ)

#print axioms fast_time_exponent_pos
#print axioms explicit_fast_time_exponent
#print axioms palasek_activation_not_wkb_small

end NSFastTimePrincipalFirewall
