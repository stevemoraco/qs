import Mathlib

namespace B4Auto20Run5

/-- BANKER: a finite-regulator lower gap `c ≤ g` transfers through a certified
approximation `|g - m| ≤ ε` to the continuum/target quantity as `c - ε ≤ m`.
This is the exact scalar stability contract needed when replacing a regulated
spectral quantity by an approximating continuum one. -/
theorem ym_approximation_error_transfers_gap
    (g m c ε : ℝ) (hgap : c ≤ g) (herr : |g - m| ≤ ε) :
    c - ε ≤ m := by
  have hupper : g - m ≤ ε := (abs_le.mp herr).2
  linarith

/-- CLEANER: if the approximation error is strictly smaller than the regulated
gap, then the transferred target gap remains strictly positive. The proof edge
therefore needs an error margin below the lower bound, not merely convergence in
some unquantified sense. -/
theorem ym_strict_error_margin_preserves_positive_gap
    (g m c ε : ℝ) (hgap : c ≤ g) (herr : |g - m| ≤ ε)
    (hmargin : ε < c) :
    0 < m := by
  have htransfer := ym_approximation_error_transfers_gap g m c ε hgap herr
  linarith

/-- CRITIC: the threshold is sharp. A positive regulated gap can collapse to a
zero target quantity when the approximation error is allowed to equal the whole
gap. -/
theorem ym_error_equal_to_gap_can_collapse_target :
    let g : ℝ := 1
    let m : ℝ := 0
    let c : ℝ := 1
    let ε : ℝ := 1
    c ≤ g ∧ |g - m| ≤ ε ∧ m = 0 := by
  norm_num

#print axioms B4Auto20Run5.ym_approximation_error_transfers_gap
#print axioms B4Auto20Run5.ym_strict_error_margin_preserves_positive_gap
#print axioms B4Auto20Run5.ym_error_equal_to_gap_can_collapse_target

end B4Auto20Run5
