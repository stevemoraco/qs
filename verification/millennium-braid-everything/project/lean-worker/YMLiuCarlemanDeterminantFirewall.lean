import Mathlib

namespace YMLiuCarlemanDeterminantFirewall

/-!
# One-dimensional counterexample to a universal Carleman determinant lower bound

For a one-dimensional operator with eigenvalue `a`, the modified Fredholm
factor is `(1-a) * exp(a)`.  At `a=1` this is zero, while every exponential
`exp(-c)` is strictly positive.  Thus Hilbert--Schmidt norm control alone cannot
supply a positive lower bound for `|det₂(I-A)|`.

This finite real-algebra file audits a claimed intermediate theorem.  It does
not construct Yang--Mills theory or prove a mass gap.
-/

/-- The one-eigenvalue modified Fredholm determinant factor. -/
def scalarDet2 (a : ℝ) : ℝ := (1 - a) * Real.exp a

/-- The squared Hilbert--Schmidt norm of the one-dimensional scalar operator. -/
def scalarHSSq (a : ℝ) : ℝ := a ^ 2

/-- At eigenvalue one, the modified determinant vanishes exactly. -/
theorem scalarDet2_one : scalarDet2 1 = 0 := by
  simp [scalarDet2]

/-- The one-dimensional operator `[1]` has squared Hilbert--Schmidt norm one. -/
theorem scalarHSSq_one : scalarHSSq 1 = 1 := by
  norm_num [scalarHSSq]

/-- For every real constant `c`, the proposed positive exponential lower bound
fails at the one-dimensional Hilbert--Schmidt operator with eigenvalue one. -/
theorem advertised_lower_bound_fails_at_one (c : ℝ) :
    ¬ (Real.exp (-c * scalarHSSq 1) ≤ |scalarDet2 1|) := by
  intro h
  have hzero : Real.exp (-c * scalarHSSq 1) ≤ 0 := by
    simpa [scalarDet2_one] using h
  exact (not_le_of_gt (Real.exp_pos (-c * scalarHSSq 1))) hzero

/-- Hence no universal constant can make the advertised inequality true for all
one-dimensional Hilbert--Schmidt operators. -/
theorem no_universal_scalar_carleman_lower_bound :
    ¬ ∃ c : ℝ, ∀ a : ℝ,
      Real.exp (-c * scalarHSSq a) ≤ |scalarDet2 a| := by
  intro h
  obtain ⟨c, hc⟩ := h
  exact advertised_lower_bound_fails_at_one c (hc 1)

/-- Norm finiteness is compatible with a zero determinant: this is the exact
finite logical obstruction to inferring invertibility from Hilbert--Schmidt
membership alone. -/
theorem finite_hs_norm_and_zero_det_coexist :
    scalarHSSq 1 = 1 ∧ scalarDet2 1 = 0 := by
  exact ⟨scalarHSSq_one, scalarDet2_one⟩

#print axioms scalarDet2_one
#print axioms scalarHSSq_one
#print axioms advertised_lower_bound_fails_at_one
#print axioms no_universal_scalar_carleman_lower_bound
#print axioms finite_hs_norm_and_zero_det_coexist

end YMLiuCarlemanDeterminantFirewall
