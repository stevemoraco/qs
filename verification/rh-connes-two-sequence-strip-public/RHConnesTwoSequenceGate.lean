import Mathlib

namespace RHConnesTwoSequenceGate

/-- Two-sided certified eigenvalue enclosures preserve a strict sector order. -/
theorem sector_order_survives_errors
    {e o eModel oModel epsE epsO : ℝ}
    (he : |e - eModel| ≤ epsE)
    (ho : |o - oModel| ≤ epsO)
    (hgap : eModel + epsE < oModel - epsO) :
    e < o := by
  have heUpper : e ≤ eModel + epsE := by
    have h := (abs_le.mp he).2
    linarith
  have hoLower : oModel - epsO ≤ o := by
    have h := (abs_le.mp ho).1
    linarith
  linarith

/--
Separate certified gaps to the next even level and to the odd-sector bottom
prove that the enclosed lowest even level is both simple and globally lowest.
-/
theorem simple_even_ground_state_of_enclosures
    {e0 e1 o0 e0Model e1Model o0Model eps0 eps1 epsOdd : ℝ}
    (he0 : |e0 - e0Model| ≤ eps0)
    (he1 : |e1 - e1Model| ≤ eps1)
    (ho0 : |o0 - o0Model| ≤ epsOdd)
    (hEvenGap : e0Model + eps0 < e1Model - eps1)
    (hOddGap : e0Model + eps0 < o0Model - epsOdd) :
    e0 < e1 ∧ e0 < o0 := by
  constructor
  · exact sector_order_survives_errors he0 he1 hEvenGap
  · exact sector_order_survives_errors he0 ho0 hOddGap

/-- The support-to-strip amplification factor is nonnegative. -/
theorem strip_amplification_nonneg (a L : ℝ) :
    0 ≤ Real.exp (a * L / 2) * Real.sqrt L := by
  exact mul_nonneg (le_of_lt (Real.exp_pos _)) (Real.sqrt_nonneg _)

/--
A spectral residual/gap estimate composes with the support-to-strip Fourier
amplification.  The analytic application uses
`amplification = exp (aL/2) * sqrt L`.
-/
theorem residual_to_strip_error
    {a L residual gap eigenvectorError stripError : ℝ}
    (heigen : eigenvectorError ≤ Real.sqrt 2 * residual / gap)
    (hstrip :
      stripError ≤
        (Real.exp (a * L / 2) * Real.sqrt L) * eigenvectorError) :
    stripError ≤
      (Real.exp (a * L / 2) * Real.sqrt L) *
        (Real.sqrt 2 * residual / gap) := by
  calc
    stripError ≤
        (Real.exp (a * L / 2) * Real.sqrt L) * eigenvectorError := hstrip
    _ ≤ (Real.exp (a * L / 2) * Real.sqrt L) *
          (Real.sqrt 2 * residual / gap) :=
      mul_le_mul_of_nonneg_left heigen (strip_amplification_nonneg a L)

/-- An explicit residual budget closes any prescribed strip tolerance. -/
theorem residual_budget_closes_strip
    {a L residual gap eigenvectorError stripError tolerance : ℝ}
    (heigen : eigenvectorError ≤ Real.sqrt 2 * residual / gap)
    (hstrip :
      stripError ≤
        (Real.exp (a * L / 2) * Real.sqrt L) * eigenvectorError)
    (hbudget :
      (Real.exp (a * L / 2) * Real.sqrt L) *
          (Real.sqrt 2 * residual / gap) < tolerance) :
    stripError < tolerance := by
  exact lt_of_le_of_lt
    (residual_to_strip_error heigen hstrip)
    hbudget

/--
The two-sequence triangle bridge: exact minimizer to candidate plus candidate
to target controls exact minimizer to target.
-/
theorem two_sequence_triangle
    {E : Type*} [SeminormedAddCommGroup E]
    {exactState candidate target : E}
    {exactCandidateError candidateTargetError : ℝ}
    (hExactCandidate :
      ‖exactState - candidate‖ ≤ exactCandidateError)
    (hCandidateTarget :
      ‖candidate - target‖ ≤ candidateTargetError) :
    ‖exactState - target‖ ≤
      exactCandidateError + candidateTargetError := by
  calc
    ‖exactState - target‖ =
        ‖(exactState - candidate) + (candidate - target)‖ := by
      congr 1
      abel
    _ ≤ ‖exactState - candidate‖ + ‖candidate - target‖ := norm_add_le _ _
    _ ≤ exactCandidateError + candidateTargetError :=
      add_le_add hExactCandidate hCandidateTarget

/-- Two half-tolerance gates compose to one full target tolerance. -/
theorem two_half_tolerances_close
    {E : Type*} [SeminormedAddCommGroup E]
    {exactState candidate target : E}
    {tolerance : ℝ}
    (hExactCandidate : ‖exactState - candidate‖ ≤ tolerance / 2)
    (hCandidateTarget : ‖candidate - target‖ ≤ tolerance / 2) :
    ‖exactState - target‖ ≤ tolerance := by
  have h := two_sequence_triangle hExactCandidate hCandidateTarget
  linarith

#print axioms sector_order_survives_errors
#print axioms simple_even_ground_state_of_enclosures
#print axioms strip_amplification_nonneg
#print axioms residual_to_strip_error
#print axioms residual_budget_closes_strip
#print axioms two_sequence_triangle
#print axioms two_half_tolerances_close

end RHConnesTwoSequenceGate
