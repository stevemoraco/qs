import Mathlib

namespace RHSingularSeriesTransportFinite

/-- The finite weighted second-difference telescope behind the origin coefficient
    in the smooth singular-series transport theorem. -/
theorem weighted_secondDifference_telescope
    (φ : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n,
      ((j + 1 : ℕ) : ℝ) *
        (φ j - 2 * φ (j + 1) + φ (j + 2)))
      = φ 0 - ((n + 1 : ℕ) : ℝ) * φ n
        + (n : ℝ) * φ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- If the last two test values vanish, the weighted second difference extracts
    exactly the origin value. -/
theorem weighted_secondDifference_extracts_origin
    (φ : ℕ → ℝ) (n : ℕ)
    (hn : φ n = 0) (hn1 : φ (n + 1) = 0) :
    (∑ j ∈ Finset.range n,
      ((j + 1 : ℕ) : ℝ) *
        (φ j - 2 * φ (j + 1) + φ (j + 2))) = φ 0 := by
  rw [weighted_secondDifference_telescope, hn, hn1]
  ring

/-- Once the diagonal and singular-series model have opposite logarithmic
    main terms, the full normalized quantity differs from the actual-minus-model
    residual only by bounded remainders. -/
theorem logarithmic_main_terms_cancel
    (A diagonal model residual c L d m : ℝ)
    (hdiag : diagonal = c * L + d)
    (hmodel : model = -c * L + m)
    (hA : A = diagonal + model + residual) :
    A = residual + d + m := by
  rw [hA, hdiag, hmodel]
  ring

/-- Capturing centered pair cancellation only through logarithmic shift `LY`
    leaves the exact logarithmic debt `c * (LN - LY)`. -/
theorem truncated_shift_debt
    (c LN LY b : ℝ) :
    c * LN + (-c * LY + b) = c * (LN - LY) + b := by
  ring

/-- At a power cutoff `Y = N^θ`, one surplus fraction `1-θ` of the diagonal
    logarithm remains. -/
theorem power_shift_debt
    (c L θ b : ℝ) :
    c * L + (-c * (θ * L) + b)
      = (1 - θ) * c * L + b := by
  ring

/-- A bounded comparison between a normalized energy and a pair residual
    transfers any upper bound on one to an upper bound on the other. -/
theorem residual_upper_of_energy_upper
    (A E C M : ℝ)
    (hcompare : |A - E| ≤ C)
    (hA : A ≤ M) :
    E ≤ M + C := by
  have hEA : E - A ≤ C := by
    calc
      E - A = -(A - E) := by ring
      _ ≤ |A - E| := neg_le_abs (A - E)
      _ ≤ C := hcompare
  linarith

/-- The reverse boundedness transfer. -/
theorem energy_upper_of_residual_upper
    (A E C M : ℝ)
    (hcompare : |A - E| ≤ C)
    (hE : E ≤ M) :
    A ≤ M + C := by
  have hAE : A - E ≤ C := le_trans (le_abs_self (A - E)) hcompare
  linarith

#print axioms weighted_secondDifference_telescope
#print axioms weighted_secondDifference_extracts_origin
#print axioms logarithmic_main_terms_cancel
#print axioms truncated_shift_debt
#print axioms power_shift_debt
#print axioms residual_upper_of_energy_upper
#print axioms energy_upper_of_residual_upper

end RHSingularSeriesTransportFinite
