import Mathlib

/-!
# Gevrey / Osterwalder--Schrader growth repair

This file formalizes only the finite real-algebra shell behind a possible
repair of the all-order source-growth step in the Kirk-v4 Yang--Mills route.

An ordinary analytic source disk gives one factorial.  A labelled-tree/contact
placement estimate can contribute a second factorial.  The product therefore
has finite Gevrey order two even when the ordinary exponential generating
series has radius zero.

The finite theorem is deliberately weaker than source analyticity and stronger
than fixed-order control: it records an all-order factorial envelope with one
source-order-independent geometric base.  To apply it to Yang--Mills one must
still prove the primitive Cauchy row, the contact/tree placement row, a linear
Schwartz-seminorm order, the passive-root atom bound, and all regulator/volume/
depth uniformities in the actual renormalized rooted Banach spaces.

This file does not formalize Osterwalder--Schrader reconstruction, Schwinger
functions, Gaussian chaos, replica--BKAR, renormalization, Yang--Mills theory,
a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.GevreyOSGrowthRepair

/-- Multiplying two nonnegative all-order bounds adds their factorial-growth
exponents and multiplies their geometric bases. -/
theorem factorial_exponents_add
    (n p q : ℕ)
    (x y A B R S : ℝ)
    (hx0 : 0 ≤ x)
    (hy0 : 0 ≤ y)
    (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (hR : 0 ≤ R)
    (hS : 0 ≤ S)
    (hx : x ≤ A * (n.factorial : ℝ) ^ p * R ^ n)
    (hy : y ≤ B * (n.factorial : ℝ) ^ q * S ^ n) :
    x * y ≤
      A * B * (n.factorial : ℝ) ^ (p + q) * (R * S) ^ n := by
  have hupperX : 0 ≤ A * (n.factorial : ℝ) ^ p * R ^ n := by
    positivity
  calc
    x * y ≤
        (A * (n.factorial : ℝ) ^ p * R ^ n) *
          (B * (n.factorial : ℝ) ^ q * S ^ n) :=
      mul_le_mul hx hy hy0 hupperX
    _ = A * B * (n.factorial : ℝ) ^ (p + q) * (R * S) ^ n := by
      rw [pow_add, mul_pow]
      ring

/-- A Cauchy factorial and an independent labelled-tree/contact factorial
produce an explicit order-two factorial envelope. -/
theorem cauchy_times_tree_is_gevrey_two
    (n : ℕ)
    (local tree total A B R S : ℝ)
    (hlocal0 : 0 ≤ local)
    (htree0 : 0 ≤ tree)
    (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (hR : 0 ≤ R)
    (hS : 0 ≤ S)
    (hlocal : local ≤ A * (n.factorial : ℝ) * R ^ n)
    (htree : tree ≤ B * (n.factorial : ℝ) * S ^ n)
    (htotal : total ≤ local * tree) :
    total ≤
      A * B * (n.factorial : ℝ) ^ 2 * (R * S) ^ n := by
  have hproduct := factorial_exponents_add
    n 1 1 local tree A B R S
    hlocal0 htree0 hA hB hR hS
    (by simpa using hlocal) (by simpa using htree)
  exact htotal.trans (by simpa using hproduct)

/-- A fixed nonnegative root/transport prefactor does not change the factorial
exponent; it only changes the leading constant. -/
theorem fixed_prefactor_preserves_gevrey_order
    (n p : ℕ)
    (base prefactor total A R : ℝ)
    (hprefactor : 0 ≤ prefactor)
    (hA : 0 ≤ A)
    (hR : 0 ≤ R)
    (hbase : base ≤ A * (n.factorial : ℝ) ^ p * R ^ n)
    (htotal : total ≤ prefactor * base) :
    total ≤
      (prefactor * A) * (n.factorial : ℝ) ^ p * R ^ n := by
  have hmul := mul_le_mul_of_nonneg_left hbase hprefactor
  exact htotal.trans (by
    calc
      prefactor * base ≤
          prefactor * (A * (n.factorial : ℝ) ^ p * R ^ n) := hmul
      _ = (prefactor * A) * (n.factorial : ℝ) ^ p * R ^ n := by
        ring)

/-- The model order-two coefficient has normalized exponential-generating
coefficient exactly `n!`.  Thus finite factorial order does not by itself imply
an ordinary positive source radius. -/
def gevreyTwoCoefficient (n : ℕ) : ℝ :=
  (n.factorial : ℝ) ^ 2

theorem gevreyTwo_normalized_coefficient (n : ℕ) :
    gevreyTwoCoefficient n / (n.factorial : ℝ) =
      (n.factorial : ℝ) := by
  have hfac : (n.factorial : ℝ) ≠ 0 := by
    positivity
  apply (div_eq_iff hfac).2
  simp [gevreyTwoCoefficient, pow_two]

/-- The normalized coefficients in the order-two model grow by the exact
factor `n+1` at the next order. -/
theorem gevreyTwo_normalized_succ (n : ℕ) :
    gevreyTwoCoefficient (n + 1) / ((n + 1).factorial : ℝ) =
      ((n + 1 : ℕ) : ℝ) *
        (gevreyTwoCoefficient n / (n.factorial : ℝ)) := by
  rw [gevreyTwo_normalized_coefficient, gevreyTwo_normalized_coefficient]
  simp [Nat.factorial_succ]

#print axioms factorial_exponents_add
#print axioms cauchy_times_tree_is_gevrey_two
#print axioms fixed_prefactor_preserves_gevrey_order
#print axioms gevreyTwo_normalized_coefficient
#print axioms gevreyTwo_normalized_succ

end Millennium.YangMills.GevreyOSGrowthRepair
