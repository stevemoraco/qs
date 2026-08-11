import Mathlib

/-!
# Yang--Mills RG clock: finite scalar cores

Honesty boundary: this file formalizes only the finite telescoping identity,
its elementary exponential window consequence, the endpoint scale-to-gap
algebra, and the exact cancellation of the linear two-loop clock coefficient.
It does not formalize a Yang--Mills coupling, beta function, step-scaling map,
trajectory summability, dimensional transmutation, a transfer Hamiltonian,
Osterwalder--Schrader reconstruction, or the Clay theorem.
-/

namespace MillenniumBraid
namespace YMRGClock

/-- One discrete RG-clock defect. -/
def defect (F : ℕ → ℝ) (ell : ℝ) (k : ℕ) : ℝ :=
  F (k + 1) - F k + ell

/-- The exact finite telescoping identity behind the matching-scale clock. -/
theorem defect_sum_telescope
    (F : ℕ → ℝ) (ell : ℝ) (N : ℕ) :
    (∑ k in Finset.range N, defect F ell k) =
      F N - F 0 + (N : ℝ) * ell := by
  induction N with
  | zero => simp [defect]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [defect]
      push_cast
      ring

/-- Rewriting the physical logarithmic scale in terms of the accumulated
clock defects and the terminal clock value. -/
theorem clock_log_identity
    (F : ℕ → ℝ) (ell : ℝ) (N : ℕ) :
    (N : ℝ) * ell - F 0 =
      (∑ k in Finset.range N, defect F ell k) - F N := by
  have h := defect_sum_telescope F ell N
  linarith

/-- A bounded accumulated defect and bounded terminal clock give a bounded
matching logarithm. -/
theorem clock_log_abs_le
    (F : ℕ → ℝ) (ell D B : ℝ) (N : ℕ)
    (hdef : |∑ k in Finset.range N, defect F ell k| ≤ D)
    (hterminal : |F N| ≤ B) :
    |(N : ℝ) * ell - F 0| ≤ D + B := by
  rw [clock_log_identity]
  calc
    |(∑ k in Finset.range N, defect F ell k) - F N|
        ≤ |∑ k in Finset.range N, defect F ell k| + |F N| := abs_sub _ _
    _ ≤ D + B := add_le_add hdef hterminal

/-- Exponentiating an absolute logarithmic bound gives a two-sided positive
multiplicative window. -/
theorem exp_abs_window
    (x C : ℝ) (h : |x| ≤ C) :
    Real.exp (-C) ≤ Real.exp x ∧ Real.exp x ≤ Real.exp C := by
  constructor
  · exact Real.exp_le_exp.mpr (neg_le_of_abs_le h)
  · exact Real.exp_le_exp.mpr (le_of_abs_le h)

/-- The finite RG-clock matching window obtained from the preceding two
lemmas. -/
theorem clock_exp_window
    (F : ℕ → ℝ) (ell D B : ℝ) (N : ℕ)
    (hdef : |∑ k in Finset.range N, defect F ell k| ≤ D)
    (hterminal : |F N| ≤ B) :
    Real.exp (-(D + B)) ≤ Real.exp ((N : ℝ) * ell - F 0) ∧
      Real.exp ((N : ℝ) * ell - F 0) ≤ Real.exp (D + B) := by
  exact exp_abs_window _ _ (clock_log_abs_le F ell D B N hdef hterminal)

/-- A matching-scale product bound converts an endpoint inverse-length gap
into a gap divided by the transmutation scale. -/
theorem endpoint_ratio_lower
    (gap Lambda m L C : ℝ)
    (hLambda : 0 < Lambda)
    (hL : 0 < L)
    (hm : 0 ≤ m)
    (hgap : m / L ≤ gap)
    (hscale : L * Lambda ≤ Real.exp C) :
    m * Real.exp (-C) ≤ gap / Lambda := by
  have hexp_nonneg : 0 ≤ Real.exp (-C) := le_of_lt (Real.exp_pos _)
  have hscaled : (L * Lambda) * Real.exp (-C) ≤ 1 := by
    calc
      (L * Lambda) * Real.exp (-C)
          ≤ Real.exp C * Real.exp (-C) :=
        mul_le_mul_of_nonneg_right hscale hexp_nonneg
      _ = 1 := by
        rw [← Real.exp_add]
        ring_nf
        simp
  have hmL : m * Real.exp (-C) * Lambda ≤ m / L := by
    apply (le_div_iff₀ hL).2
    have hmul := mul_le_mul_of_nonneg_left hscaled hm
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
  apply (le_div_iff₀ hLambda).2
  calc
    (m * Real.exp (-C)) * Lambda ≤ m / L := by
      simpa [mul_assoc] using hmL
    _ ≤ gap := hgap

/-- Exact algebraic cancellation of the linear reciprocal-clock and
logarithmic-clock terms for a two-loop step map.  The analytic Taylor
remainder estimate is deliberately outside this finite theorem. -/
theorem two_loop_linear_cancellation
    (a b ell u : ℝ) (ha : a ≠ 0) :
    (ell / a) * (a ^ 2 - b) * u +
      (ell * (b - a ^ 2) / a ^ 2) * a * u = 0 := by
  field_simp [ha]
  ring

#print axioms defect_sum_telescope
#print axioms clock_log_identity
#print axioms clock_log_abs_le
#print axioms exp_abs_window
#print axioms clock_exp_window
#print axioms endpoint_ratio_lower
#print axioms two_loop_linear_cancellation

end YMRGClock
end MillenniumBraid