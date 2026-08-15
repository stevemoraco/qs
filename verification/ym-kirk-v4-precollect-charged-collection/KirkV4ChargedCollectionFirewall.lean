import Mathlib

namespace Millennium.YangMills

/-!
# Kirk v4 charged-collection firewall

Finite obstruction and repair criterion for the proposed strategy of paying the
Qref pivot-incidence charge before canonical hull collection.

Paying `exp (lambda * n)` atomwise before collection is not, by itself, enough
if the later collected object is reweighted by a larger incidence count.  A
plain norm-nonincreasing regrouping controls the unweighted absolute row, but a
charged norm can increase when collection enlarges pivot incidence.

The repair is exact: either collection must not increase the incidence used by
the charged norm, or each atom must retain enough unused exponential slack to
pay the incidence increment introduced by its final collected hull.

This file is a finite logical firewall only.  It does not assert that Kirk v4's
actual canonical collection realizes the hostile model, and it encodes no
continuum, OS, mass-gap, or Clay conclusion.
-/

/-- Replacing incidence one by incidence two strictly increases the exponential
charge whenever the charge parameter is positive.  This is the two-positive-
atom hostile model behind the collection firewall. -/
theorem postcollect_incidence_growth_strict
    (lambda : ℝ) (hlambda : 0 < lambda) :
    2 * Real.exp lambda < 2 * Real.exp (2 * lambda) := by
  have hlt : lambda < 2 * lambda := by
    linarith
  have hexp : Real.exp lambda < Real.exp (2 * lambda) :=
    Real.exp_lt_exp.mpr hlt
  exact mul_lt_mul_of_pos_left hexp (by norm_num)

/-- A charged collection step is automatically safe if the incidence assigned
after collection does not exceed the incidence already charged atomwise. -/
theorem charged_collection_safe_if_incidence_nonincreasing
    (lambda base nAtom nFinal : ℝ)
    (hlambda : 0 ≤ lambda)
    (hbase : 0 ≤ base)
    (hinc : nFinal ≤ nAtom) :
    Real.exp (lambda * nFinal) * base ≤
      Real.exp (lambda * nAtom) * base := by
  have harg : lambda * nFinal ≤ lambda * nAtom :=
    mul_le_mul_of_nonneg_left hinc hlambda
  have hexp : Real.exp (lambda * nFinal) ≤ Real.exp (lambda * nAtom) :=
    Real.exp_le_exp.mpr harg
  exact mul_le_mul_of_nonneg_right hexp hbase

/-- More generally, an incidence increase introduced by collection is harmless
if unused exponential slack pays exactly that increment. -/
theorem collection_incidence_increment_paid_by_slack
    (lambda base nAtom nFinal slack : ℝ)
    (hbase : 0 ≤ base)
    (hpay : lambda * nFinal ≤ lambda * nAtom + slack) :
    Real.exp (lambda * nFinal) * (Real.exp (-slack) * base) ≤
      Real.exp (lambda * nAtom) * base := by
  have harg : lambda * nFinal + (-slack) ≤ lambda * nAtom := by
    linarith
  have hexp :
      Real.exp (lambda * nFinal + (-slack)) ≤ Real.exp (lambda * nAtom) :=
    Real.exp_le_exp.mpr harg
  calc
    Real.exp (lambda * nFinal) * (Real.exp (-slack) * base)
        = Real.exp (lambda * nFinal + (-slack)) * base := by
            rw [Real.exp_add]
            ring
    _ ≤ Real.exp (lambda * nAtom) * base :=
      mul_le_mul_of_nonneg_right hexp hbase

/-- A concrete two-atom recharge statement: two positive atoms individually
charged at incidence one can become strictly more expensive if collected into
one object that is charged at incidence two. -/
theorem two_atom_recharge_counterexample
    (lambda : ℝ) (hlambda : 0 < lambda) :
    Real.exp (lambda * 1) + Real.exp (lambda * 1) <
      2 * Real.exp (lambda * 2) := by
  simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using
    postcollect_incidence_growth_strict lambda hlambda

#print axioms postcollect_incidence_growth_strict
#print axioms charged_collection_safe_if_incidence_nonincreasing
#print axioms collection_incidence_increment_paid_by_slack
#print axioms two_atom_recharge_counterexample

end Millennium.YangMills
