import Mathlib

/-!
# Finite-degree polynomial roots satisfy an all-derivative factorial envelope

Finite real-algebra reduction for the primitive passive-root row in a rooted
replica--BKAR expansion.

A fixed local polynomial root has only finitely many nonzero field-derivative
rows.  For any positive derivative-radius parameter `sigma`, the weighted sum
of those finitely many rows gives one explicit constant that controls every
order by the standard factorial/Cauchy shape

`row q <= A * q! / sigma^q`.

This separates two issues that must not be conflated:

* finite polynomial degree automatically removes the all-order derivative
  tail; but
* the finitely many regulator-weighted derivative rows still have to be
  proved uniformly for the actual Yang--Mills root atoms.

The file does not formalize polynomials on gauge fields, Gaussian regulators,
replica--BKAR, Kirk's Banach spaces, renormalization, continuum limits,
Osterwalder--Schrader reconstruction, Yang--Mills theory, a mass gap, or a Clay
theorem.
-/

namespace Millennium.YangMills.FinitePolynomialRootFactorialEnvelope

open scoped BigOperators

/--
The explicit factorial-envelope constant for a nonnegative derivative row
supported in orders `0, ..., degree`.
-/
noncomputable def factorialEnvelopeConstant
    (row : ℕ → ℝ) (degree : ℕ) (sigma : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (degree + 1),
    row q * sigma ^ q / (Nat.factorial q : ℝ)

/-- The explicit finite-degree envelope constant is nonnegative. -/
theorem factorialEnvelopeConstant_nonneg
    (row : ℕ → ℝ) (degree : ℕ) (sigma : ℝ)
    (hrow : ∀ q, 0 ≤ row q)
    (hsigma : 0 ≤ sigma) :
    0 ≤ factorialEnvelopeConstant row degree sigma := by
  unfold factorialEnvelopeConstant
  apply Finset.sum_nonneg
  intro q hq
  apply div_nonneg
  · exact mul_nonneg (hrow q) (pow_nonneg hsigma q)
  · positivity

/--
A nonnegative row that vanishes above a fixed degree obeys a factorial
majorant at every derivative order.  The parameter `sigma` may be any positive
number; changing it only changes the explicit finite constant.
-/
theorem finite_degree_factorial_envelope
    (row : ℕ → ℝ) (degree : ℕ) (sigma : ℝ)
    (hrow : ∀ q, 0 ≤ row q)
    (hzero : ∀ q, degree < q → row q = 0)
    (hsigma : 0 < sigma) :
    ∀ q,
      row q ≤
        factorialEnvelopeConstant row degree sigma *
            (Nat.factorial q : ℝ) /
          sigma ^ q := by
  intro q
  have hA : 0 ≤ factorialEnvelopeConstant row degree sigma :=
    factorialEnvelopeConstant_nonneg row degree sigma hrow hsigma.le
  have hfac_nonneg : 0 ≤ (Nat.factorial q : ℝ) := by positivity
  have hsigma_pow_pos : 0 < sigma ^ q := pow_pos hsigma q
  by_cases hq : q ≤ degree
  · have hmem : q ∈ Finset.range (degree + 1) := by
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hq)
    have hterm_nonneg :
        ∀ i ∈ Finset.range (degree + 1),
          0 ≤ row i * sigma ^ i / (Nat.factorial i : ℝ) := by
      intro i hi
      apply div_nonneg
      · exact mul_nonneg (hrow i) (pow_nonneg hsigma.le i)
      · positivity
    have hterm_le :
        row q * sigma ^ q / (Nat.factorial q : ℝ) ≤
          factorialEnvelopeConstant row degree sigma := by
      unfold factorialEnvelopeConstant
      exact Finset.single_le_sum hterm_nonneg hmem
    have hfac_pos : 0 < (Nat.factorial q : ℝ) := by positivity
    have hscaled :
        row q * sigma ^ q ≤
          factorialEnvelopeConstant row degree sigma *
            (Nat.factorial q : ℝ) :=
      (div_le_iff₀ hfac_pos).mp hterm_le
    exact (le_div_iff₀ hsigma_pow_pos).2 <| by
      simpa [mul_assoc] using hscaled
  · have hdegree_lt : degree < q := Nat.lt_of_not_ge hq
    rw [hzero q hdegree_lt]
    exact div_nonneg (mul_nonneg hA hfac_nonneg) hsigma_pow_pos.le

/--
At unit derivative radius, the same theorem has the simpler form
`row q <= A * q!`.
-/
theorem finite_degree_unit_radius_envelope
    (row : ℕ → ℝ) (degree : ℕ)
    (hrow : ∀ q, 0 ≤ row q)
    (hzero : ∀ q, degree < q → row q = 0) :
    ∀ q,
      row q ≤
        factorialEnvelopeConstant row degree 1 *
          (Nat.factorial q : ℝ) := by
  intro q
  have h :=
    finite_degree_factorial_envelope row degree 1 hrow hzero (by norm_num) q
  simpa using h

/--
Finite sums of independently certified root rows preserve the same factorial
shape.  This is the scalar shadow of taking a fixed finite marked root family.
-/
theorem add_factorial_envelopes
    (row₁ row₂ : ℕ → ℝ) (A₁ A₂ sigma : ℝ)
    (hsigma : 0 < sigma)
    (h₁ : ∀ q, row₁ q ≤ A₁ * (Nat.factorial q : ℝ) / sigma ^ q)
    (h₂ : ∀ q, row₂ q ≤ A₂ * (Nat.factorial q : ℝ) / sigma ^ q) :
    ∀ q,
      row₁ q + row₂ q ≤
        (A₁ + A₂) * (Nat.factorial q : ℝ) / sigma ^ q := by
  intro q
  have hsigma_pow_pos : 0 < sigma ^ q := pow_pos hsigma q
  have hadd := add_le_add (h₁ q) (h₂ q)
  apply (le_div_iff₀ hsigma_pow_pos).2
  have hscaled := mul_le_mul_of_nonneg_right hadd hsigma_pow_pos.le
  field_simp at hscaled ⊢
  linarith

#print axioms factorialEnvelopeConstant_nonneg
#print axioms finite_degree_factorial_envelope
#print axioms finite_degree_unit_radius_envelope
#print axioms add_factorial_envelopes

end Millennium.YangMills.FinitePolynomialRootFactorialEnvelope
