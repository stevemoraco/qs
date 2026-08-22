import Mathlib

/-!
# RH universal doubling-window finite core

Finite real-order/calculus-free algebra for the human-level universal doubling
criterion banked in `stevemoraco/RH`.

This file does **not** formalize the von Mangoldt function, the Riemann zeta
function, Suzuki's explicit formula, the reciprocal-square zero sum, or RH.
It formalizes only:

* finite dyadic descent from a one-step reserve;
* negativity after a finite reserve budget is exhausted;
* the affine slope numerator on one fixed event cell;
* uniqueness of the critical-coordinate sign change;
* the nonnegative entropy gap `r - 1 - log r`;
* positivity of the weighted excess above the cell minimum.
-/

namespace RHUniversalDoublingFinite

/-- A uniform one-step doubling reserve telescopes exactly along every finite
    dyadic ray. -/
theorem dyadic_descent
    (F : ℝ → ℝ) (d x : ℝ)
    (hstep : ∀ y : ℝ, F (2 * y) ≤ F y - d) :
    ∀ n : ℕ, F ((2 : ℝ) ^ n * x) ≤ F x - (n : ℝ) * d := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        F ((2 : ℝ) ^ (n + 1) * x)
            = F (2 * ((2 : ℝ) ^ n * x)) := by
                congr 1
                rw [pow_succ]
                ring
        _ ≤ F ((2 : ℝ) ^ n * x) - d := hstep _
        _ ≤ (F x - (n : ℝ) * d) - d := sub_le_sub_right ih d
        _ = F x - ((n + 1 : ℕ) : ℝ) * d := by
              push_cast
              ring

/-- Once the accumulated dyadic reserve exceeds the starting budget, the
    statistic is strictly negative on that dyadic iterate. -/
theorem dyadic_negative_after_budget
    (F : ℝ → ℝ) (d x M : ℝ) (n : ℕ)
    (hstep : ∀ y : ℝ, F (2 * y) ≤ F y - d)
    (hstart : F x ≤ M)
    (hbudget : M < (n : ℝ) * d) :
    F ((2 : ℝ) ^ n * x) < 0 := by
  have hdesc := dyadic_descent F d x hstep n
  linarith

/-- The numerator governing the derivative of the finite event-cell profile in
    square-root coordinate.  In the arithmetic application `c = sqrt 2 - 1`
    and `S` is the frozen weighted mass in `(x,2x]`. -/
def slopeNumerator (c S y : ℝ) : ℝ := 2 * c * y - S

/-- The advertised event-cell critical coordinate makes the slope vanish. -/
theorem critical_slope_zero
    {c S ystar : ℝ}
    (hS : S = 2 * c * ystar) :
    slopeNumerator c S ystar = 0 := by
  unfold slopeNumerator
  rw [hS]
  ring

/-- To the left of the critical coordinate the slope is nonpositive. -/
theorem slope_nonpos_left
    {c S y ystar : ℝ}
    (hc : 0 ≤ c)
    (hy : y ≤ ystar)
    (hS : S = 2 * c * ystar) :
    slopeNumerator c S y ≤ 0 := by
  have hc2 : 0 ≤ 2 * c := by linarith
  have hmul : 2 * c * y ≤ 2 * c * ystar :=
    mul_le_mul_of_nonneg_left hy hc2
  unfold slopeNumerator
  rw [hS]
  linarith

/-- To the right of the critical coordinate the slope is nonnegative. -/
theorem slope_nonneg_right
    {c S y ystar : ℝ}
    (hc : 0 ≤ c)
    (hy : ystar ≤ y)
    (hS : S = 2 * c * ystar) :
    0 ≤ slopeNumerator c S y := by
  have hc2 : 0 ≤ 2 * c := by linarith
  have hmul : 2 * c * ystar ≤ 2 * c * y :=
    mul_le_mul_of_nonneg_left hy hc2
  unfold slopeNumerator
  rw [hS]
  linarith

/-- The scalar convexity inequality controlling the exact excess above the
    unique event-cell minimum. -/
theorem entropy_gap_nonneg
    {r : ℝ} (hr : 0 < r) :
    0 ≤ r - 1 - Real.log r := by
  have hlog : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr
  linarith

/-- Multiplying the entropy gap by the natural nonnegative event-cell weight
    preserves its sign. -/
theorem weighted_entropy_excess_nonneg
    {c ystar r : ℝ}
    (hc : 0 ≤ c) (hystar : 0 ≤ ystar) (hr : 0 < r) :
    0 ≤ 4 * c * ystar * (r - 1 - Real.log r) := by
  have hgap := entropy_gap_nonneg hr
  have hcoef : 0 ≤ 4 * c * ystar := by positivity
  exact mul_nonneg hcoef hgap

/-- Elementary reserve accounting used in the RH->doubling direction after the
    deterministic drift and two absolute loss bounds have been separated. -/
theorem reserve_after_two_losses
    {drift reserve zeroLoss tailLoss : ℝ}
    (h : reserve + zeroLoss + tailLoss ≤ drift) :
    reserve ≤ drift - zeroLoss - tailLoss := by
  linarith

#print axioms dyadic_descent
#print axioms dyadic_negative_after_budget
#print axioms critical_slope_zero
#print axioms slope_nonpos_left
#print axioms slope_nonneg_right
#print axioms entropy_gap_nonneg
#print axioms weighted_entropy_excess_nonneg
#print axioms reserve_after_two_losses

end RHUniversalDoublingFinite
