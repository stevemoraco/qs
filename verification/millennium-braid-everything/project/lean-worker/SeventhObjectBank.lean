import Mathlib

namespace SeventhObjectBank

/-- One-step relative-error closure. If the inherited transverse defect uses
at most a `ρ` fraction of the safety margin and the new error uses at most an
`ε` fraction, then the margin closes whenever `ρ + ε ≤ 1`. -/
theorem one_step_margin_closure
    {transverse error margin ρ ε : ℝ}
    (hmargin : 0 ≤ margin)
    (hρ : 0 ≤ ρ)
    (htransverse : transverse ≤ ρ * margin)
    (herror : error ≤ ε * margin)
    (hbudget : ρ + ε ≤ 1) :
    transverse + error ≤ margin := by
  calc
    transverse + error ≤ ρ * margin + ε * margin := add_le_add htransverse herror
    _ = (ρ + ε) * margin := by ring
    _ ≤ 1 * margin := mul_le_mul_of_nonneg_right hbudget hmargin
    _ = margin := by ring

/-- Discrete invariant-tube theorem for a scale-compatible certificate.
If every scale satisfies

`E (n+1) ≤ ρ * E n + ε * margin`

with nonnegative contraction factor `ρ` and `ρ + ε ≤ 1`, then any initial
defect inside the margin remains inside it at every scale.  This is the
abstract finite-to-infinite error-budget firewall used by the seventh-object
program; it does not assert that any Millennium-problem-specific object
satisfies the recurrence. -/
theorem invariant_margin_tube
    (E : ℕ → ℝ)
    {margin ρ ε : ℝ}
    (hmargin : 0 ≤ margin)
    (hρ : 0 ≤ ρ)
    (hbudget : ρ + ε ≤ 1)
    (h0 : E 0 ≤ margin)
    (hstep : ∀ n : ℕ, E (n + 1) ≤ ρ * E n + ε * margin) :
    ∀ n : ℕ, E n ≤ margin := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
      have hρE : ρ * E n ≤ ρ * margin :=
        mul_le_mul_of_nonneg_left ih hρ
      calc
        E (n + 1) ≤ ρ * E n + ε * margin := hstep n
        _ ≤ ρ * margin + ε * margin := add_le_add_right hρE (ε * margin)
        _ = (ρ + ε) * margin := by ring
        _ ≤ 1 * margin := mul_le_mul_of_nonneg_right hbudget hmargin
        _ = margin := by ring

/-- Strict one-step contraction relative to the margin.  This records the
quantitative version needed when the accumulated orthogonal defect must shrink
rather than merely stay bounded. -/
theorem strict_relative_contraction
    {oldDefect newDefect margin ρ ε q : ℝ}
    (hmargin : 0 ≤ margin)
    (hold : oldDefect ≤ margin)
    (hρ : 0 ≤ ρ)
    (hstep : newDefect ≤ ρ * oldDefect + ε * margin)
    (hq : ρ + ε ≤ q) :
    newDefect ≤ q * margin := by
  have hρold : ρ * oldDefect ≤ ρ * margin :=
    mul_le_mul_of_nonneg_left hold hρ
  calc
    newDefect ≤ ρ * oldDefect + ε * margin := hstep
    _ ≤ ρ * margin + ε * margin := add_le_add_right hρold (ε * margin)
    _ = (ρ + ε) * margin := by ring
    _ ≤ q * margin := mul_le_mul_of_nonneg_right hq hmargin

/-- A positive surviving gap `gap - totalDefect` forces the strict budget
`totalDefect < gap`.  Mere finiteness of the defect is not enough. -/
theorem positive_surviving_gap_requires_strict_budget
    {gap totalDefect : ℝ}
    (hsurvive : 0 < gap - totalDefect) :
    totalDefect < gap := by
  linarith

/-- Explicit finite-defect counterexample: a finite defect can exceed a
positive initial gap and destroy positivity. -/
theorem finite_defect_can_destroy_gap :
    ¬ (0 < (1 : ℝ) - 2) := by
  norm_num

/-- A strict contraction factor cannot preserve a fixed positive floor even
for one exact error-free step: `c * ρ < c` whenever `c>0` and `ρ<1`. -/
theorem strict_contraction_loses_fixed_floor
    {c ρ : ℝ}
    (hc : 0 < c)
    (hρ : ρ < 1) :
    c * ρ < c := by
  simpa using mul_lt_mul_of_pos_left hρ hc

#print axioms one_step_margin_closure
#print axioms invariant_margin_tube
#print axioms strict_relative_contraction
#print axioms positive_surviving_gap_requires_strict_budget
#print axioms finite_defect_can_destroy_gap
#print axioms strict_contraction_loses_fixed_floor

end SeventhObjectBank
