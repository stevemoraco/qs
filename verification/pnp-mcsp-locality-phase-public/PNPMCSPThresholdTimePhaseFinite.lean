import Mathlib

namespace PNPMCSPThresholdTimePhaseFinite

/-!
Finite real-exponent shadow of the CHMY one-tape MCSP parameter ledger.

The human note in `stevemoraco/RH` audits the published local-PRG proof and
records that its certified superlinear region has `tau < 2 * mu`, where `tau`
is the truth-table time exponent and `mu` is the MCSP circuit-threshold
exponent.  This file proves only the resulting real inequalities.

It does not define MCSP, Turing machines, PRGs, circuit complexity, hardness
magnification, `P`, or `NP`, and it does not formalize the imported source
theorems.
-/

/-- Strict exponent region certified by the published local-PRG parameter
choice. -/
def publishedPhase (tau mu : ℝ) : Prop :=
  1 < tau ∧ tau < 2 * mu

/-- Every superlinear point below the line `tau = 2 mu` lies above threshold
exponent `1/2`. -/
theorem publishedPhase_above_half
    {tau mu : ℝ} (h : publishedPhase tau mu) :
    (1 : ℝ) / 2 < mu := by
  rcases h with ⟨htau, hline⟩
  linarith

/-- No threshold exponent at most `1/2` belongs to the strict published
superlinear phase. -/
theorem no_small_threshold_publishedPhase
    {tau mu : ℝ} (hmu : mu ≤ (1 : ℝ) / 2) :
    ¬ publishedPhase tau mu := by
  intro hphase
  have habove := publishedPhase_above_half hphase
  linarith

/-- The phase line can equivalently be read as a locality exponent inequality. -/
theorem phase_line_iff
    {tau mu : ℝ} :
    tau < 2 * mu ↔ tau / 2 < mu := by
  constructor <;> intro h <;> linarith

/-- A weak certificate at time exponent at least `1.01` forces threshold
exponent at least `0.505`. -/
theorem terminal_101_weak_boundary
    {tau mu : ℝ}
    (htau : (101 : ℝ) / 100 ≤ tau)
    (hline : tau ≤ 2 * mu) :
    (101 : ℝ) / 200 ≤ mu := by
  linarith

/-- A strict certificate at time exponent at least `1.01` forces threshold
exponent strictly above `0.505`. -/
theorem terminal_101_strict_boundary
    {tau mu : ℝ}
    (htau : (101 : ℝ) / 100 ≤ tau)
    (hline : tau < 2 * mu) :
    (101 : ℝ) / 200 < mu := by
  linarith

/-- A fixed positive exponent gap survives every additive exponent slack that
is smaller than that gap. No separate sign assumption on the slack is needed. -/
theorem fixed_gap_cannot_be_hidden
    {tau mu epsilon : ℝ}
    (hepsilon_small : epsilon < (tau - 1) / 2)
    (hcertificate : tau / 2 - epsilon ≤ mu) :
    (1 : ℝ) / 2 < mu := by
  linarith

/-- General replacement-generator locality exponent. -/
def localityExponent (theta tau eta : ℝ) : ℝ :=
  theta * tau + eta

/-- Separating an independent polynomial overhead is exact algebra. -/
theorem design_equation_subtract_overhead
    {theta tau eta mu : ℝ} :
    localityExponent theta tau eta < mu ↔
      theta * tau < mu - eta := by
  unfold localityExponent
  constructor <;> intro h <;> linarith

/-- At positive time exponent, the design equation solves exactly for the
required time-to-locality exponent `theta`. -/
theorem design_equation_solve_theta
    {theta tau eta mu : ℝ} (htau : 0 < tau) :
    localityExponent theta tau eta < mu ↔
      theta < (mu - eta) / tau := by
  constructor
  · intro h
    apply (lt_div_iff₀ htau).2
    exact (design_equation_subtract_overhead.mp h)
  · intro h
    apply design_equation_subtract_overhead.mpr
    exact (lt_div_iff₀ htau).1 h

/-- The square-root-time certificate is exactly the exponent `tau/2` when
there is no independent polynomial overhead. -/
theorem square_root_certificate_exponent (tau : ℝ) :
    localityExponent ((1 : ℝ) / 2) tau 0 = tau / 2 := by
  unfold localityExponent
  ring

/-- Substituting the square-root certificate into the general design equation
recovers the phase line. -/
theorem square_root_design_iff
    {tau mu : ℝ} :
    localityExponent ((1 : ℝ) / 2) tau 0 < mu ↔
      tau < 2 * mu := by
  rw [square_root_certificate_exponent]
  exact phase_line_iff.symm

/-- For every `mu>1/2`, there is a concrete superlinear exponent strictly
inside the phase region. -/
theorem publishedPhase_nonempty_above_half
    {mu : ℝ} (hmu : (1 : ℝ) / 2 < mu) :
    publishedPhase (mu + (1 : ℝ) / 2) mu := by
  unfold publishedPhase
  constructor <;> linarith

#print axioms publishedPhase_above_half
#print axioms no_small_threshold_publishedPhase
#print axioms phase_line_iff
#print axioms terminal_101_weak_boundary
#print axioms terminal_101_strict_boundary
#print axioms fixed_gap_cannot_be_hidden
#print axioms design_equation_subtract_overhead
#print axioms design_equation_solve_theta
#print axioms square_root_certificate_exponent
#print axioms square_root_design_iff
#print axioms publishedPhase_nonempty_above_half

end PNPMCSPThresholdTimePhaseFinite
