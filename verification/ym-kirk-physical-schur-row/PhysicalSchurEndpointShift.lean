import Mathlib

/-!
# Physical Schur endpoint-shift firewall

Finite real-analysis bridge for the physical Schur row used in the continuum
Yang--Mills connector.  A fixed physical endpoint radius in a kernel of the
form `exp (-m * (d - 2R)_+)` changes only the prefactor relative to the pure
physical exponential `exp (-m*d)`; it cannot weaken the decay rate or create a
cutoff-density factor once the Riemann weight is already present.

This file does not prove Kirk's connector estimate, Riemann-sum integrability,
polymer/BKAR bounds, continuum convergence, Osterwalder--Schrader
reconstruction, a Yang--Mills mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills

open scoped BigOperators

/-- A fixed endpoint shift in the positive-part exponential costs at most the
fixed prefactor `exp (2*m*R)` and preserves the decay exponent `m`. -/
theorem shifted_exp_kernel_le_prefactor
    {m R d : ℝ} (hm : 0 ≤ m) :
    Real.exp (-m * max (d - 2 * R) 0) ≤
      Real.exp (2 * m * R) * Real.exp (-m * d) := by
  have hmax : d - 2 * R ≤ max (d - 2 * R) 0 := le_max_left _ _
  have hmul : m * (d - 2 * R) ≤ m * max (d - 2 * R) 0 :=
    mul_le_mul_of_nonneg_left hmax hm
  have hneg : -m * max (d - 2 * R) 0 ≤ -m * (d - 2 * R) := by
    linarith
  have hexp : Real.exp (-m * max (d - 2 * R) 0) ≤
      Real.exp (-m * (d - 2 * R)) :=
    Real.exp_monotone hneg
  calc
    Real.exp (-m * max (d - 2 * R) 0)
        ≤ Real.exp (-m * (d - 2 * R)) := hexp
    _ = Real.exp (2 * m * R) * Real.exp (-m * d) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Finite-row form: the endpoint-shifted exponential row is bounded by the
same pure exponential row times one fixed prefactor. -/
theorem shifted_exp_finite_row_le
    {ι : Type} [Fintype ι]
    (dist : ι → ℝ) {m R A : ℝ}
    (hm : 0 ≤ m) (hA : 0 ≤ A) :
    (∑ i, A * Real.exp (-m * max (dist i - 2 * R) 0)) ≤
      Real.exp (2 * m * R) *
        (∑ i, A * Real.exp (-m * dist i)) := by
  have hpoint : ∀ i,
      A * Real.exp (-m * max (dist i - 2 * R) 0) ≤
        Real.exp (2 * m * R) * (A * Real.exp (-m * dist i)) := by
    intro i
    have h := shifted_exp_kernel_le_prefactor (m := m) (R := R) (d := dist i) hm
    have hA' := mul_le_mul_of_nonneg_left h hA
    calc
      A * Real.exp (-m * max (dist i - 2 * R) 0)
          ≤ A * (Real.exp (2 * m * R) * Real.exp (-m * dist i)) := hA'
      _ = Real.exp (2 * m * R) * (A * Real.exp (-m * dist i)) := by ring
  calc
    (∑ i, A * Real.exp (-m * max (dist i - 2 * R) 0))
        ≤ ∑ i, Real.exp (2 * m * R) *
          (A * Real.exp (-m * dist i)) :=
      Finset.sum_le_sum fun i hi => hpoint i
    _ = Real.exp (2 * m * R) *
        (∑ i, A * Real.exp (-m * dist i)) := by
      rw [Finset.mul_sum]

/-- Riemann-weighted finite-row form.  If the pure physical exponential row
has a regulator-uniform weighted bound `B`, then the endpoint-shifted row has
the regulator-uniform bound `exp (2*m*R) * B`. -/
theorem shifted_exp_weighted_row_le
    {ι : Type} [Fintype ι]
    (dist : ι → ℝ) {m R A w B : ℝ}
    (hm : 0 ≤ m) (hA : 0 ≤ A) (hw : 0 ≤ w)
    (hbase :
      w * (∑ i, A * Real.exp (-m * dist i)) ≤ B) :
    w * (∑ i, A * Real.exp (-m * max (dist i - 2 * R) 0)) ≤
      Real.exp (2 * m * R) * B := by
  have hsum := shifted_exp_finite_row_le dist hm hA
  have hw_sum :
      w * (∑ i, A * Real.exp (-m * max (dist i - 2 * R) 0)) ≤
        w * (Real.exp (2 * m * R) *
          (∑ i, A * Real.exp (-m * dist i))) :=
    mul_le_mul_of_nonneg_left hsum hw
  calc
    w * (∑ i, A * Real.exp (-m * max (dist i - 2 * R) 0))
        ≤ w * (Real.exp (2 * m * R) *
          (∑ i, A * Real.exp (-m * dist i))) := hw_sum
    _ = Real.exp (2 * m * R) *
        (w * (∑ i, A * Real.exp (-m * dist i))) := by ring
    _ ≤ Real.exp (2 * m * R) * B :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le

#print axioms shifted_exp_kernel_le_prefactor
#print axioms shifted_exp_finite_row_le
#print axioms shifted_exp_weighted_row_le

end Millennium.YangMills
