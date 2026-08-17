import Mathlib

/-!
# Faizal--Shabir OS quotient-identification firewall

Finite quadratic-form countermodel for a continuum Osterwalder--Schrader
identification step. Pointwise convergence of positive quadratic forms to a
limit form does not imply that a vector null for the limit form is already null
for every approximating form. Hence the naive map from the limit quotient to
finite quotients is not automatically well-defined.

This file formalizes only finite real algebra. It does not formalize Schwinger
functions, reflection positivity, varying Hilbert spaces, Mosco convergence,
Yang--Mills theory, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirOSQuotientFirewall

/-- Limit quadratic form with a hidden null direction. -/
def qLimit (v : ℝ × ℝ) : ℝ := v.1 ^ 2

/-- Approximating positive quadratic form which weakly lifts the hidden direction. -/
def qApprox (ε : ℝ) (v : ℝ × ℝ) : ℝ := v.1 ^ 2 + ε * v.2 ^ 2

/-- The hidden coordinate is exactly null in the limit form. -/
theorem hidden_direction_limit_null :
    qLimit (0, 1) = 0 := by
  norm_num [qLimit]

/-- For every positive approximation parameter, the same vector has positive finite-form norm. -/
theorem hidden_direction_approx_positive
    (ε : ℝ) (hε : 0 < ε) :
    0 < qApprox ε (0, 1) := by
  simpa [qApprox] using hε

/-- A domination estimate by the limit form forces exact null-space inclusion. -/
theorem domination_forces_exact_null
    (qk qInf M : ℝ)
    (hqk : 0 ≤ qk)
    (hdom : qk ≤ M * qInf)
    (hzero : qInf = 0) :
    qk = 0 := by
  rw [hzero, mul_zero] at hdom
  linarith

/-- Pointwise-small positive lift of a limit-null direction defeats every finite domination constant. -/
theorem positive_hidden_direction_not_dominated
    (ε M : ℝ) (hε : 0 < ε) :
    ¬ qApprox ε (0, 1) ≤ M * qLimit (0, 1) := by
  simp [qApprox, qLimit]
  linarith

/-- Equality relation induced by the limit null space in this model. -/
def limitEq (u v : ℝ × ℝ) : Prop := u.1 = v.1

/-- Equality relation induced by an approximating positive form. -/
def approxEq (ε : ℝ) (u v : ℝ × ℝ) : Prop :=
  qApprox ε (u.1 - v.1, u.2 - v.2) = 0

/-- Zero and the hidden vector represent the same limit quotient class. -/
theorem zero_hidden_same_limit_class :
    limitEq (0, 0) (0, 1) := by
  simp [limitEq]

/-- For positive ε, those representatives are distinct in the approximating quotient. -/
theorem zero_hidden_distinct_approx_class
    (ε : ℝ) (hε : 0 < ε) :
    ¬ approxEq ε (0, 0) (0, 1) := by
  simp [approxEq, qApprox]
  linarith

/-- A positive hidden lift can be arbitrarily small while remaining nonzero. -/
theorem small_positive_hidden_lift
    (δ : ℝ) (hδ : 0 < δ) :
    0 < qApprox (δ / 2) (0, 1) ∧ qApprox (δ / 2) (0, 1) < δ := by
  constructor <;> simp [qApprox] <;> linarith

#print axioms hidden_direction_limit_null
#print axioms hidden_direction_approx_positive
#print axioms domination_forces_exact_null
#print axioms positive_hidden_direction_not_dominated
#print axioms zero_hidden_same_limit_class
#print axioms zero_hidden_distinct_approx_class
#print axioms small_positive_hidden_lift

end Millennium.YangMills.FaizalShabirOSQuotientFirewall
